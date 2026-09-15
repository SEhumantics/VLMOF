import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "experiments" / "run_fifth_evaluation.py"
SPEC = importlib.util.spec_from_file_location("fifth_evaluation", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class TimingScheduleTest(unittest.TestCase):
    def test_timeout_output_bytes_are_decoded_for_evidence_files(self):
        self.assertEqual("bad\ufffd", MODULE.output_text(b"bad\xff"))
        self.assertEqual("", MODULE.output_text(None))

    def test_each_cell_receives_both_orders_and_full_counterbalanced_schedule(self):
        cells = [("a", 10), ("a", 100), ("b", 10), ("b", 100)]
        schedule = MODULE.timing_schedule(cells, 5)
        self.assertEqual(20, len(schedule))
        self.assertEqual(cells, [cell for trial, cell, _ in schedule if trial == 1])
        self.assertEqual(list(reversed(cells)), [cell for trial, cell, _ in schedule if trial == 2])
        for cell in cells:
            orders = [order for _, observed, order in schedule if observed == cell]
            self.assertEqual(5, len(orders))
            self.assertEqual({2, 3}, {orders.count("emf-first"), orders.count("vlmof-first")})


if __name__ == "__main__":
    unittest.main()
