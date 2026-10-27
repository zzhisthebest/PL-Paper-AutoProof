import unittest
from unittest.mock import patch

import analyze_problems as analysis


class AnalysisTests(unittest.TestCase):
    def test_page_body_must_be_complete(self):
        self.assertEqual(analysis.complete_pages('Characters [0, 5) of 10\nabcde\nnext_offset: 5\n'), [(0, 5, 10)])
        self.assertEqual(analysis.complete_pages('Characters [5, 10) of 10\n中文abc\nEND_OF_TRACE\n'), [(5, 10, 10)])
        self.assertEqual(analysis.complete_pages('Characters [0, 5) of 10\nab\nnext_offset: 5\n'), [])

    def test_stop_kills_all_active_process_groups(self):
        class Child:
            pid = 123456
        child = Child()
        analysis.PROCESSES.add(child)
        try:
            with patch.object(analysis.os, 'killpg') as kill:
                analysis.stop_children()
                kill.assert_called_once_with(child.pid, analysis.signal.SIGKILL)
                self.assertTrue(analysis.STOP.is_set())
        finally:
            analysis.PROCESSES.remove(child)
            analysis.STOP.clear()
