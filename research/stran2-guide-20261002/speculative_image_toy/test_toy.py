#!/usr/bin/env python3
import copy
from pathlib import Path
import tempfile
import unittest
import run_toy as toy


class ToyTests(unittest.TestCase):
    def test_exhaustive_reset_image_and_free_witness(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'toy.aig'
            graph = toy.build_toy()
            toy.write_aig(path, graph)
            decoded = toy.read_aig(path)
            self.assertEqual(decoded['outputs'], [12, 14])
            self.assertEqual(len(decoded['gates']), 11)
            proof = toy.exhaustive(decoded)
            self.assertEqual(proof['transition_rows'], 64)
            self.assertEqual(proof['image_rows'], 512)
            self.assertEqual(proof['reset_rows'], 8)
            self.assertEqual(proof['free_witnesses'], 32)

    def test_transition_mutation_is_detected(self):
        graph = toy.build_toy()
        graph['latches'][2] = 12
        with self.assertRaisesRegex(ValueError, 'equations'):
            toy.exhaustive(graph)

    def test_nonzero_reset_is_rejected(self):
        graph = toy.build_toy()
        graph['reset'][0] = 1
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, 'zero reset'):
                toy.write_aig(Path(directory) / 'toy.aig', graph)

    def test_dense_topology_rejects_cycle(self):
        graph = toy.build_toy()
        graph['gates'][0] = (14, 8)
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, 'cyclic'):
                toy.write_aig(Path(directory) / 'toy.aig', graph)

    def test_pair_comparison_includes_phase(self):
        self.assertEqual(toy.pair_status(dict(outputs=[7, 7]))['status'], 'MERGED')
        self.assertEqual(toy.pair_status(dict(outputs=[6, 7]))['status'], 'NOT_MERGED')

    def test_dsec_exit_zero_is_not_pass(self):
        self.assertEqual(toy.dsec_status('EXIT', 'nothing'), 'INCONCLUSIVE')
        self.assertEqual(toy.dsec_status('ERROR', 'Networks are equivalent'), 'ERROR')
        self.assertEqual(toy.dsec_status('EXIT', 'Networks are equivalent'), 'PASS')
        self.assertEqual(toy.dsec_status('EXIT', 'Networks are NOT EQUIVALENT'), 'FAIL')

    def test_source_consistent_speculative_witness(self):
        state, inputs = (1, 1, 0), (0, 0, 0)
        outputs, nexts = toy.expected(state, inputs)
        self.assertNotEqual(outputs[0], outputs[1])
        self.assertEqual(nexts[2], nexts[0] & nexts[1])
        e, u, v = inputs
        speculative_c_next = (u & v) if e else state[2]
        self.assertNotEqual(speculative_c_next, nexts[0] & nexts[1])


if __name__ == '__main__':
    unittest.main()
