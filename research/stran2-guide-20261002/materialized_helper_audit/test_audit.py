#!/usr/bin/env python3
import json
import os
from types import SimpleNamespace
from pathlib import Path
import tempfile
import unittest
import audit

P, PROD, AT = audit.load_runtime(Path(os.environ.get('STRAN2_FROZEN_PACKAGE', Path(__file__).resolve().parent.parent)))


class MaterializedGraphTests(unittest.TestCase):
    def graph(self, directory):
        path = Path(directory) / 'original.aig'
        PROD.write_aig(path, dict(ni=1, nl=1, gates=[(4, 2)], outputs=[6], latches=[2]))
        return P.Aiger(path)

    def candidate(self):
        return dict(root=3, recipe=[3, 4], out=-2,
                    free_witness=dict(inputs=[1], state=[1], root=1, replacement=0))

    def test_preserves_original_transition_and_outputs(self):
        with tempfile.TemporaryDirectory() as directory:
            a = self.graph(directory)
            graph, pairs = audit.materialize(a, [self.candidate()], P)
            self.assertEqual(graph['gates'][0], a.gates[0])
            self.assertEqual(graph['outputs'], [6, 6, 8])
            self.assertEqual(graph['latches'], [2])
            self.assertEqual(pairs[0]['live_appended_nodes'], [4])
            path = Path(directory) / 'augmented.aig'
            PROD.write_aig(path, graph)
            checked = audit.audit_materialization(a, P.Aiger(path), [self.candidate()], pairs, P)
            self.assertEqual(checked['free_witnesses'], 1)
            self.assertEqual(audit.inspect_pairs(P.Aiger(path), pairs)[0]['status'], 'NOT_MERGED')

    def test_complemented_helper_uses_original_source_ids(self):
        with tempfile.TemporaryDirectory() as directory:
            a = self.graph(directory)
            candidate = self.candidate()
            candidate.update(recipe=[2, 4], out=-3)
            graph, pairs = audit.materialize(a, [candidate], P)
            self.assertEqual(len(graph['gates']), 1)
            self.assertEqual(pairs[0]['helper_literal'], 7)
            self.assertEqual(graph['outputs'], [6, 6, 7])

    def test_rejects_cyclic_divisor(self):
        with tempfile.TemporaryDirectory() as directory:
            a = self.graph(directory)
            candidate = self.candidate()
            candidate['recipe'] = [2, 6]
            with self.assertRaisesRegex(ValueError, 'cyclic'):
                audit.materialize(a, [candidate], P)

    def test_rejects_mismatched_witness(self):
        with tempfile.TemporaryDirectory() as directory:
            a = self.graph(directory)
            candidate = self.candidate()
            graph, pairs = audit.materialize(a, [candidate], P)
            path = Path(directory) / 'augmented.aig'
            PROD.write_aig(path, graph)
            candidate['free_witness']['replacement'] = 1
            with self.assertRaisesRegex(ValueError, 'witness identity'):
                audit.audit_materialization(a, P.Aiger(path), [candidate], pairs, P)

    def test_pair_equality_includes_complemented_phase(self):
        pair = dict(index=0, root=3, root_po_index=0, helper_po_index=1)
        self.assertEqual(audit.inspect_pairs(SimpleNamespace(outputs=[7, 7]), [pair])[0]['status'], 'MERGED')
        self.assertEqual(audit.inspect_pairs(SimpleNamespace(outputs=[6, 7]), [pair])[0]['status'], 'NOT_MERGED')

    def test_empty_selection_is_exact_original(self):
        with tempfile.TemporaryDirectory() as directory:
            a = self.graph(directory)
            graph, pairs = audit.materialize(a, [], P)
            self.assertEqual(graph, dict(ni=a.ni, nl=a.nl, gates=a.gates, outputs=a.outputs, latches=a.latches))
            self.assertEqual(pairs, [])


if __name__ == '__main__':
    unittest.main()
