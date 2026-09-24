"""Exhaustive independent oracle for the production teaching lookup."""
import ctypes
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


@unittest.skipUnless(shutil.which("cc"), "requires C compiler")
class TeachingLookupTest(unittest.TestCase):
    def test_every_assignment_and_hypothesis(self):
        source = (Path(__file__).resolve().parents[1] /
                  "src/proof/cec/cecTranCex.h").read_text()
        add = source[source.index("static inline void Cec_TranTeachCoverAdd"):
                     source.index("static unsigned Cec_TranTeachMix")]
        lookup = source[source.index("static word const * Cec_TranTeachCoverLookup"):
                        source.index("// When more CEX traces")]
        shim = ("#include <assert.h>\n#include <stdint.h>\ntypedef uint64_t word;\n"
                + add + lookup +
                "\nword cover(int n,int a,int k){return Cec_TranTeachCoverLookup(n,a)[k];}\n")
        with tempfile.TemporaryDirectory() as directory:
            library = Path(directory)/"teaching.so"
            subprocess.run(["cc", "-shared", "-fPIC", "-x", "c", "-", "-o", str(library)],
                           input=shim, text=True, check=True, capture_output=True)
            cover = ctypes.CDLL(str(library)).cover
            cover.argtypes = [ctypes.c_int]*3
            cover.restype = ctypes.c_uint64
            for n in range(9):
                for assignment in range(1 << (n+1)):
                    target = assignment >> n
                    bits = [(assignment >> i) & 1 for i in range(n)]
                    hypotheses = [0, 1]
                    for bit in bits:
                        hypotheses.extend((bit, 1-bit))
                    for i in range(n):
                        for j in range(i+1, n):
                            for result in (bits[i] & bits[j], bits[i] | bits[j],
                                           bits[i] ^ bits[j]):
                                hypotheses.extend((result, 1-result))
                    expected = sum((v != target) << i for i, v in enumerate(hypotheses))
                    actual = sum(cover(n, assignment, k) << (64*k) for k in range(3))
                    self.assertEqual(actual, expected, (n, assignment))


if __name__ == "__main__":
    unittest.main()
