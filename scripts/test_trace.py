import unittest

from analyze_trace import compare, first_loss, head


class TraceTests(unittest.TestCase):
    def test_partition_is_transitive(self):
        self.assertEqual(head({4: 3, 3: 0}, 4), 0)
        with self.assertRaises(AssertionError):
            head({4: 3, 3: 4}, 4)

    def test_loss_is_before_unknown_cleanup(self):
        c = {"a": 8, "b": 0}
        b = {"classes": [
            {"pairs": {4: 0}, "point": "seed", "round": -1},
            {"pairs": {}, "point": "resim-frame-0", "round": 2},
            {"pairs": {}, "point": "after-check", "round": 2}], "sat": []}
        self.assertEqual(first_loss(b, c)["point"], "resim-frame-0")

    def test_same_recipe_survives_slot_reordering(self):
        c = {"target": 4, "kind": 2, "out": -2, "recipe": (2, 4),
             "slot": 0, "helper": 0, "a": 8, "b": 12}
        b = {"info": {"and": 10, "regs": 2, "cands": 1},
             "candidates": {0: c}, "results": {0: {"proved": 1}}}
        a = {**b, "candidates": {9: {**c, "slot": 9}},
             "results": {9: {"proved": 1}}}
        result = compare(b, a)
        self.assertEqual(result["common"], 1)
        self.assertEqual(result["lost_proved"], [])


if __name__ == "__main__":
    unittest.main()
