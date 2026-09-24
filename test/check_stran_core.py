#!/usr/bin/env python3
"""Compare the actual C core selector with an independent OFF x ON oracle.

The oracle counts opposite-label observation pairs, including multiplicity;
it does not reproduce the C implementation's unresolved-group partitioning.
Run from any directory. CC/CFLAGS select the small temporary C-shim build.
This tests selector semantics, not formal equivalence of optimized circuits.
"""
import collections
import ctypes
import hashlib
import json
import os
from pathlib import Path
import random
import re
import shlex
import subprocess
import tempfile


SEED = 747118613
NAME = "Cec_TranSelectCareObservedCoreExcept"
SOURCE = Path(__file__).resolve().parents[1] / "src/proof/cec/cecTranBuild.h"
MASK = (1 << 64) - 1


def extract_selector(source):
    # Remove comments/literals only from the brace-counting view, preserving
    # offsets so the compiled function is the verbatim production source.
    pattern = r'/\*.*?\*/|//[^\n]*|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\''
    view = re.sub(pattern, lambda m: " " * len(m.group()), source, flags=re.S)
    match = re.search(r"static\s+int\s+" + NAME + r"\s*\(", view)
    if match is None:
        raise RuntimeError("Cannot find selector in " + str(SOURCE))
    start = view.index("{", match.end())
    depth = 0
    for end in range(start, len(view)):
        depth += (view[end] == "{") - (view[end] == "}")
        if depth == 0:
            return source[match.start():end + 1]
    raise RuntimeError("Unclosed selector body")


SHIM = r"""
#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
typedef uint64_t word;
typedef struct { int nSlots; word *pSims; } Cec_TranSim_t;
typedef struct { int nSize, nCap; int *pArray; } Vec_Int_t;
#define ABC_ALLOC(type, n) ((type *)malloc(sizeof(type) * (size_t)(n)))
#define ABC_CALLOC(type, n) ((type *)calloc((size_t)(n), sizeof(type)))
#define ABC_FREE(p) do { free(p); (p) = NULL; } while (0)
#define Abc_MinInt(a, b) ((a) < (b) ? (a) : (b))
#define Abc_MaxInt(a, b) ((a) > (b) ? (a) : (b))
static int Abc_TtCountOnes(word w) { return __builtin_popcountll(w); }
static int Vec_IntSize(Vec_Int_t *v) { return v->nSize; }
static int Vec_IntEntry(Vec_Int_t *v, int i)
{ assert(i >= 0 && i < v->nSize); return v->pArray[i]; }
static void Vec_IntClear(Vec_Int_t *v) { v->nSize = 0; }
static void Vec_IntPush(Vec_Int_t *v, int i)
{ assert(v->nSize < v->nCap); v->pArray[v->nSize++] = i; }
static word *Cec_TranSimObj(Cec_TranSim_t *s, int obj)
{ return s->pSims + (size_t)obj * s->nSlots; }
"""

ENTRY = r"""
int check_selector(int slots, int divs, int bound, int forbidden,
                   word *columns, word *care, int *core, int *size)
{
    Cec_TranSim_t sim = {slots, columns};
    Vec_Int_t pool = {divs, divs, ABC_ALLOC(int, divs)};
    Vec_Int_t result = {0, 8, core};
    int i, ret;
    for (i = 0; i < divs; i++) pool.pArray[i] = i + 1;
    ret = Cec_TranSelectCareObservedCoreExcept(&sim, 0, &pool, bound,
                                               &result, forbidden, care);
    *size = result.nSize;
    ABC_FREE(pool.pArray);
    return ret;
}
"""


def opposite_pairs(target, divisors, care, bits):
    # Aggregate equal rows but keep their exact multiplicities. A pair's XOR
    # records precisely which divisors separate it, regardless of group IDs.
    labels = [collections.Counter(), collections.Counter()]
    for sample in range(bits):
        if care is not None and not (care >> sample) & 1:
            continue
        row = sum(((column >> sample) & 1) << i
                  for i, column in enumerate(divisors))
        labels[(target >> sample) & 1][row] += 1
    pairs = collections.Counter()
    for off, off_count in labels[0].items():
        for on, on_count in labels[1].items():
            pairs[off ^ on] += off_count * on_count
    return pairs


def reference(pairs, divs, bound, forbidden):
    unresolved = pairs
    core = []
    while unresolved and len(core) < bound:
        best, best_score = -1, 0
        for rank in range(divs):
            if rank == forbidden or rank in core:
                continue
            score = sum(count for mask, count in unresolved.items()
                        if mask & (1 << rank))
            if score > best_score:
                best, best_score = rank, score
        if best < 0:
            break
        core.append(best)
        unresolved = {mask: count for mask, count in unresolved.items()
                      if not mask & (1 << best)}
    return (-1 if unresolved else len(core)), core


def columns_from_rows(rows, divs, slots):
    target, columns = 0, [0] * divs
    for sample in range(64 * slots):
        row, label = rows[sample % len(rows)]
        target |= label << sample
        for rank in range(divs):
            columns[rank] |= ((row >> rank) & 1) << sample
    return target, columns


def matrices():
    # Complete 8-input parity reaches the exact core bound; the independent
    # label fixture leaves all 256 groups mixed after the eighth split.
    fixed = [
        ("constant-zero", [(0, 0), (7, 0)], 3, 1),
        ("constant-one", [(0, 1), (7, 1)], 3, 2),
        ("empty-pool", [(0, 0), (0, 1)], 0, 1),
        ("inseparable", [(0, 0), (0, 1)], 4, 2),
        ("equal-complement-ties", [(4, 0), (3, 1)], 3, 3),
        ("partial-then-fail", [(0, 0), (0, 1), (3, 1)], 2, 2),
        ("unequal-multiplicity", [(0, 0)] * 9 + [(1, 1)] * 3
         + [(2, 1), (7, 0), (5, 1)], 3, 3),
        ("parity-eight", [(r, r.bit_count() % 2) for r in range(256)], 8, 4),
        ("bound-eight-failure", [(r & 255, r >> 8) for r in range(512)], 8, 8),
        ("word-partitioned", [(r, r.bit_count() % 2)
                              for r in range(36) for _ in range(64)], 6, 36),
    ]
    for name, rows, divs, slots in fixed:
        target, columns = columns_from_rows(rows, divs, slots)
        bits = 64 * slots
        full = (1 << bits) - 1
        masks = [None, 0, full, sum(1 << i for i in range(0, bits, 17)),
                 full ^ sum(1 << i for i in range(0, bits, 11)), target]
        for i, care in enumerate(masks):
            yield name + "/care-" + str(i), target, columns, care, slots
    rng = random.Random(SEED)
    for case in range(64):
        divs, slots = rng.randint(1, 14), rng.randint(1, 3)
        # Repeated and conflicting rows exercise multiplicity and failure;
        # full random columns exercise many distinct opposite-label pairs.
        rows = [(rng.getrandbits(divs), rng.randrange(2))
                for _ in range(rng.randint(2, 64 * slots))]
        target, columns = columns_from_rows(rows, divs, slots)
        if divs > 2 and case % 3 == 0:
            columns[-1] = columns[0]
            columns[-2] = columns[0] ^ ((1 << (64 * slots)) - 1)
        care = rng.getrandbits(64 * slots) if case % 2 else None
        yield "random-" + str(case), target, columns, care, slots


def main():
    source = SOURCE.read_text()
    selector = extract_selector(source)
    compiler = shlex.split(os.environ.get("CC", "cc"))
    flags = shlex.split(os.environ.get("CFLAGS", "-O2 -Wall -Wextra"))
    counts = collections.Counter()
    # The default follows tempfile/TMPDIR; callers may select owned /dev/shm.
    with tempfile.TemporaryDirectory(prefix="stran-core-check-") as scratch:
        c_path, lib_path = Path(scratch) / "core.c", Path(scratch) / "core.so"
        c_path.write_text(SHIM + "\n" + selector + "\n" + ENTRY)
        command = compiler + flags + ["-std=c99", "-shared", "-fPIC",
                                     str(c_path), "-o", str(lib_path)]
        subprocess.run(command, check=True)
        library = ctypes.CDLL(str(lib_path))
        call = library.check_selector
        ints, words = ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_uint64)
        call.argtypes = [ctypes.c_int] * 4 + [words, words, ints, ints]
        call.restype = ctypes.c_int
        assert reference({1: 3, 2: 3}, 2, 1, -1) == (-1, [0])
        assert reference({1: 3, 2: 3}, 2, 2, -1) == (2, [0, 1])
        assert reference({0: 1, 1: 2}, 1, 8, -1) == (-1, [0])
        for name, target, columns, care, slots in matrices():
            counts["matrices"] += 1
            flattened = [(column >> (64 * s)) & MASK
                         for column in [target] + columns for s in range(slots)]
            data = (ctypes.c_uint64 * len(flattened))(*flattened)
            mask = None if care is None else (ctypes.c_uint64 * slots)(
                *((care >> (64 * s)) & MASK for s in range(slots)))
            pairs = opposite_pairs(target, columns, care, 64 * slots)
            forbidden = sorted({-1, 0, len(columns) // 2, len(columns) - 1})
            for bound in range(1, 9):
                for excluded in forbidden:
                    expected = reference(pairs, len(columns), bound, excluded)
                    core, size = (ctypes.c_int * 8)(), ctypes.c_int()
                    result = call(slots, len(columns), bound, excluded,
                                  data, mask, core, ctypes.byref(size))
                    actual = result, list(core)[:size.value]
                    if actual != expected:
                        raise AssertionError(dict(case=name, bound=bound,
                            forbidden=excluded, expected=expected, actual=actual,
                            target=hex(target), columns=list(map(hex, columns)),
                            care=None if care is None else hex(care)))
                    counts["checks"] += 1
                    counts["exact" if result >= 0 else "incomplete"] += 1
                    counts["incomplete_nonempty"] += result < 0 and size.value > 0
        assert counts["exact"] and counts["incomplete_nonempty"]
    print(json.dumps(dict(status="PASS", seed=SEED, **counts,
        source=str(SOURCE), source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        selector_sha256=hashlib.sha256(selector.encode()).hexdigest(),
        compiler=compiler, flags=flags), indent=2))


if __name__ == "__main__":
    main()
