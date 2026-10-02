"""Isolated diagnostic utilities. All writes require a new file or output tree."""
from __future__ import annotations
import hashlib
import importlib
import json
import os
from pathlib import Path
import sys
import time
sys.dont_write_bytecode = True
if sys.flags.optimize != 0:
    raise RuntimeError("Python assertions must remain enabled; optimized execution is unsupported")
HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
CASES = ('045_mem_ctrl', '060_wb_dma', '034_b20_opt', '041_des_area')
REVIEW_SHA256 = '98615417a23ad6e634a195bf742081cee4d277b094d1f56ec9dfc0cb5bb34cca'
SNAPSHOT_FILES = ('frozen_inputs.json', 'A_candidates.json', 'A_roots.jsonl',
                  'result.json', 'new_identity_filter_traces.json')
RUNTIME = ('nonlinear_divisors/prototype.py', 'seq_cut_image/diagnose.py',
           'seq_care_synthesis/scan_exact_care.py', 'seq_care_synthesis/guide.py',
           'teacher_adaptive_tools/teacher_bmc.py')
SENTINELS = ((1263, (393, 2502, -2, 2516), -4),
             (1263, (393, 2503, -3, 2516), -4),
             (1263, (393, 2516, -2, 2502), -4))

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for data in iter(lambda: f.read(1048576), b''):
            h.update(data)
    return h.hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()

def write_new(path, value):
    with Path(path).open('x') as f:
        json.dump(value, f, sort_keys=True, indent=2)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())

def cid(c):
    return c['root'], tuple(c['recipe']), c['out']

def source_manifest():
    return {p.name: sha(p) for p in sorted(HERE.iterdir())
            if p.is_file() and p.suffix in ('.py', '.c', '.sh', '.json', '.md')
            and p.name not in ('authentication.json', 'validation.json', 'build_identity.json', 'source_manifest.json')}

class Deadline:
    def __init__(self, end):
        self.end = end
    def remaining(self):
        remaining = self.end - time.monotonic()
        if remaining <= 0:
            raise TimeoutError('hard total case deadline exhausted')
        return remaining

class Bindings:
    def __init__(self, files=None):
        self.files = dict(files or {})
    def add(self, path, expected=None):
        path = Path(path)
        require(path.is_file() and not path.is_symlink(), f'missing or symlink source: {path}')
        h = sha(path)
        require(expected is None or h == expected, f'identity mismatch: {path}')
        key = str(path.resolve())
        require(key not in self.files or self.files[key] == h, f'rebound source: {path}')
        self.files[key] = h
        return h
    def check(self, deadline=None):
        for path, expected in self.files.items():
            if deadline:
                deadline.remaining()
            require(Path(path).is_file() and not Path(path).is_symlink(), f'missing/symlink source: {path}')
            require(sha(path) == expected, f'bound file changed: {path}')

def authenticate(case, deadline=None):
    require(case in CASES, 'case outside frozen protocol')
    base = PACKAGE / 'free_domain_diagnostic'
    review = base / 'independent_review.json'
    bindings = Bindings()
    bindings.add(review, REVIEW_SHA256)
    ledger = read(review)['evidence_manifest']
    snapshot = base / 'runs/diagnostic-v1' / case
    for name in SNAPSHOT_FILES:
        path = snapshot / name
        expected = ledger.get(str(path.resolve()))
        require(expected is not None, f'snapshot absent from original review: {path}')
        bindings.add(path, expected)
    frozen = read(snapshot / 'frozen_inputs.json')
    require(read(snapshot / 'result.json')['status'] == 'COMPLETE', 'saved case incomplete')
    require(len(frozen['roots']) == 32 and len({r['root'] for r in frozen['roots']}) == 32,
            'frozen roots not 32 unique ordered roots')
    expected_cfg = dict(pool_cap=24, reservoir_cap=128, tfi_depth=6, peer_hops=1,
                        alias_cap=8, max_gates=2, candidates_per_root=8, lanes=256,
                        seed=2026100201, wall_seconds=120.0)
    require(frozen['case'] == case and frozen['config'] == expected_cfg, 'frozen case/config changed')
    require(frozen['initial_free_mask'] == (1 << 256)-1, 'initial free domain is not 256 lanes')
    require(digest(dict(seq=frozen['sequence_signatures'], mask=frozen['sequence_mask'])) ==
            frozen['sequence_sha256'], 'sequence snapshot digest mismatch')
    require(digest(dict(free=frozen['initial_free_signatures'], mask=frozen['initial_free_mask'])) ==
            frozen['arms']['A']['free_domain_sha256'], 'free snapshot digest mismatch')
    for path, expected in frozen['source_hashes'].items():
        if deadline:
            deadline.remaining()
        bindings.add(path, expected)  # Missing historical data is an error, never regenerated.
    bindings.add(frozen['input'], frozen['input_sha256'])
    candidates = read(snapshot / 'A_candidates.json')
    require(len(candidates) == read(snapshot / 'result.json')['arms']['A']['candidates'], 'saved baseline count mismatch')
    return frozen, candidates, snapshot, bindings

def load_runtime(frozen):
    matches = [Path(k) for k in frozen['source_hashes'] if k.endswith('/source/nonlinear_divisors/prototype.py')]
    require(len(matches) == 1, 'ambiguous frozen runtime')
    root = matches[0].parent.parent
    for name in RUNTIME:
        path = root / name
        require(str(path) in frozen['source_hashes'] and sha(path) == frozen['source_hashes'][str(path)],
                f'unbound runtime source: {path}')
    sys.path.insert(0, str(root / 'nonlinear_divisors'))
    p = importlib.import_module('prototype')
    require(Path(p.__file__).resolve() == matches[0].resolve(), 'different runtime already imported')
    for module_name, name in [('diagnose', 'seq_cut_image/diagnose.py'),
                             ('scan_exact_care', 'seq_care_synthesis/scan_exact_care.py'),
                             ('guide', 'seq_care_synthesis/guide.py'),
                             ('teacher_bmc', 'teacher_adaptive_tools/teacher_bmc.py')]:
        require(Path(sys.modules[module_name].__file__).resolve() == (root/name).resolve(),
                f'dependency from different runtime: {module_name}')
    return p
