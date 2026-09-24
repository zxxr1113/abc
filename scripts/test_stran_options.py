"""CLI contract tests; set ABC_BIN to a freshly built host-local binary."""
import os
from pathlib import Path
import subprocess
import unittest


ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("ABC_BIN"), "requires explicit ABC_BIN")
class StranOptionsTest(unittest.TestCase):
    def command(self, command, env=None):
        result = subprocess.run([os.environ["ABC_BIN"], "-q", command],
                                cwd=ROOT, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                timeout=30)
        self.assertGreaterEqual(result.returncode, 0, result.stdout)
        return result.stdout

    def test_rejects_invalid_numbers_and_trailing_arguments(self):
        for option in "YRFCSNQWKBTDVLOHZEqwjbae":
            for value in ("garbage", "2junk", "2147483648", "-2147483649", ""):
                with self.subTest(option=option, value=value):
                    out = self.command(f"&stran2 -{option} {value}")
                    self.assertIn("usage: &stran2", out)
                    self.assertNotIn("There is no AIG", out)
        self.assertIn("usage: &stran2", self.command("&stran2 unwanted"))

    def test_named_option_validation(self):
        for option in ("unknown=1", "window-factor=2", "window-cache=-1",
                       "window-F=0", "strict-S=-2", "profile=unknown",
                       "spatial-depth=3", "window-B=8x", "window-cache-MiB=-1"):
            self.assertIn("usage: &stran2", self.command(f"&stran2 -A {option}"))
        self.assertIn("Window options require -k",
                      self.command("&stran2 -A window-cache=1"))
        self.assertIn("spatial window",
                      self.command("&stran2 -k -J -A window-factor=1"))
        self.assertIn("usage: &stran2", self.command("&stran2 -Y 1 -R 27 -q 0"))

    def test_environment_and_index_validation(self):
        for name in ("ABC_CEX_MODE", "ABC_CEX_COMPRESS", "ABC_STRICT_CEX_MODE"):
            for value in ("2junk", "999999999999999999999", "-1"):
                env = dict(os.environ, **{name: value})
                self.assertIn(name + " must be an integer", self.command("&stran2", env))
        self.assertIn("observation index range",
                      self.command("&stran2 -Q 2147483647 -W 2"))

    def test_output_cap_and_numeric_endpoints(self):
        out = self.command("read_blif test/stran_seq.blif; strash; &get; "
                           "&stran -q 1 -Y 1 -R 27 -A output-L=1")
        self.assertNotIn("usage:", out)
        self.assertNotIn("Assertion", out)
        self.assertIn("There is no AIG", self.command("&stran2 -S -1 -C 0 -w 0"))
        self.assertIn("There is no AIG", self.command("&stran2 -C 2147483647"))
        self.assertIn("usage:", self.command("&stran2 -C -2147483648"))

    def test_scope_and_override_precedence(self):
        prefix = "read_blif test/stran_seq.blif; strash; &get; "
        out = self.command(prefix + "&stran -k -J -E 8388608 "
                           "-A profile=strict-speed -A window-B=7 -A window-q=2 "
                           "-A window-S=-1 -L 1")
        self.assertIn("stran-strict options: S=0 w=3.", out)
        self.assertIn("stran-window options: S=-1 cache=0 factor=0.", out)
        self.assertIn("q=2 B=7", out)
        out = self.command(prefix + "&stran2 -F 2 -C 1000 "
                           "-A initial-F=1 -A initial-C=200")
        self.assertIn("stran2 initial scorr config: F=1 C=200.", out)
        out = self.command(prefix + "&stran -A profile=strict-speed -A profile=quality")
        self.assertIn("stran-strict options: S=-1 w=8.", out)

    def test_cache_and_factor_opt_in(self):
        prefix = "read_blif test/stran_seq.blif; strash; &get; "
        out = self.command(prefix + "&stran -k -J -L 1 -p "
                           "-A spatial-depth=4 -A window-cache=1 -A window-factor=1")
        self.assertIn("stran-window options: S=-1 cache=1 factor=1.", out)
        self.assertIn("window-native-cache budget:", out)


if __name__ == "__main__":
    unittest.main()
