import json
import unittest

from timeline import build_timeline


class TimingTests(unittest.TestCase):
    def test_thinking_uses_recorded_duration(self):
        records = [dict(type='assistant', thinking_duration_ms=372123,
                        message={'content': [{'type': 'thinking', 'thinking': 'plan'}]})]
        group = build_timeline([json.dumps(r) for r in records], [])[0]
        self.assertEqual(group['durationSeconds'], 372.123)

    def test_tool_pairs_call_and_result_despite_interleaving(self):
        records = [
            dict(type='assistant', timestamp='2026-10-24T01:00:00Z',
                 message={'content': [{'type': 'tool_use', 'id': 'a', 'name': 'Bash'}]}),
            dict(type='assistant', timestamp='2026-10-24T01:00:02Z',
                 message={'content': [{'type': 'text', 'text': 'waiting'}]}),
            dict(type='user', timestamp='2026-10-24T01:00:05Z',
                 message={'content': [{'type': 'tool_result', 'tool_use_id': 'a'}]}),
        ]
        groups = build_timeline([json.dumps(r) for r in records], [])
        self.assertEqual(groups[-1]['durationSeconds'], 5)
        self.assertEqual(groups[-1]['elapsedSeconds'], 5)
        self.assertEqual(groups[0]['elapsedSeconds'], 2)
        self.assertIsNone(groups[0]['durationSeconds'])

    def test_missing_duration_is_not_zero(self):
        group = build_timeline([json.dumps(dict(type='assistant', message={
            'content': [{'type': 'thinking', 'thinking': 'plan'}]}))], [])[0]
        self.assertIsNone(group['durationSeconds'])
        self.assertIsNone(group['elapsedSeconds'])

    def test_first_thinking_counts_towards_elapsed(self):
        records = [dict(type='assistant', timestamp='2026-10-24T01:05:00Z',
                        thinking_duration_ms=300000,
                        message={'content': [{'type': 'thinking', 'thinking': 'plan'}]})]
        group = build_timeline([json.dumps(r) for r in records], [])[0]
        self.assertEqual(group['elapsedSeconds'], 300)
