#!/usr/bin/env python3
"""Portable helpers must not require the unbundled original-host manifest."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
PACKAGE = Path(__file__).resolve().parent


def load_guide():
    spec = importlib.util.spec_from_file_location(
        'portable_test_guide', PACKAGE / 'seq_care_synthesis/guide.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class PortableImports(unittest.TestCase):
    def test_cli_help_without_original_host(self):
        for relative in ('run_cut_image.py', 'seq_cut_image/selftest.py',
                         'seq_care_synthesis/guide.py'):
            with self.subTest(script=relative):
                result = subprocess.run(
                    [sys.executable, '-B', str(PACKAGE / relative), '--help'],
                    capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('usage:', result.stdout)

    def test_helpers_without_original_host(self):
        guide = load_guide()
        with tempfile.TemporaryDirectory() as temp:
            guide.OLD = Path(temp) / 'missing-original-host'
            output = Path(temp) / 'result.json'
            guide.write_json(output, {'answer': 42})
            self.assertEqual(json.loads(output.read_text()), {'answer': 42})
            self.assertEqual(guide.sha(output),
                             hashlib.sha256(output.read_bytes()).hexdigest())
            self.assertEqual(guide.dsec_answer({'status': 'exit'},
                                              'Networks are equivalent.'), 'pass')
            self.assertEqual(guide._legacy_context.cache_info().currsize, 0)

    def test_missing_legacy_context_fails_explicitly(self):
        guide = load_guide()
        with tempfile.TemporaryDirectory() as temp:
            guide.OLD = Path(temp) / 'missing-original-host'
            for action in (guide.cases, lambda: guide.COMMAND, lambda: guide.ENV,
                           lambda: guide.execute(None)):
                with self.subTest(action=action):
                    with self.assertRaisesRegex(
                            FileNotFoundError, 'Original-host experiment manifest required'):
                        action()

    def test_original_host_command_and_environment_are_preserved(self):
        guide = load_guide()
        with tempfile.TemporaryDirectory() as temp:
            guide.OLD = Path(temp)
            path = guide.OLD / 'joint_baseline/manifest.json'
            path.parent.mkdir()
            manifest = {'command': 'frozen exact command; do not substitute',
                        'prefix_env': {'ABC_CEX_SAVED': '17', 'ABC_STRICT_GUIDE': '1',
                                       'ABC_STRAN_PAPER_SKIP_SEQ': '1', 'PREFIX_ONLY': 'yes'}}
            path.write_text(json.dumps(manifest))
            expected = {**guide._CLEAN_ENV, **manifest['prefix_env'],
                        'ABC_STRAN_PAPER_SKIP_SEQ': '0', 'ABC_STRICT_GUIDE': '0'}
            self.assertEqual(guide.COMMAND, manifest['command'])
            self.assertEqual(guide.ENV, expected)
            self.assertIs(guide.ENV, guide.ENV)
            path.write_text(json.dumps({'command': 'changed after snapshot'}))
            self.assertEqual(guide.COMMAND, manifest['command'])


if __name__ == '__main__':
    unittest.main()
