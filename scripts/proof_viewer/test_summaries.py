import json
from pathlib import Path
import tempfile
import unittest

from summaries import attach_summaries, event_key
from summarize import full_trace, source_step
from read_trace import read_page


class SummaryTests(unittest.TestCase):
    def test_pages_preserve_every_character(self):
        text = '中文与 PL terms\\n' * 10000
        offset, pages = 0, []
        while offset < len(text):
            page, offset = read_page(text, offset, 12000)
            pages.append(page)
        self.assertEqual(''.join(pages), text)
        self.assertEqual(read_page(text, len(text), 12000), ('', len(text)))

    def run_data(self):
        raw = [json.dumps({'type': 'assistant', 'message': {'content': [
            {'type': 'thinking', 'thinking': 'Maybe the hypothesis is too weak.',
             'signature': 'opaque'}]}})]
        return {'raw': raw, 'repeat': 12, 'timeline': [
            {'kind': 'thinking', 'lines': [1]}, {'kind': 'archive', 'lines': []}]}

    def test_summary_requires_exact_source_match(self):
        run = self.run_data()
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / 'case'
            path.mkdir()
            key = event_key(run['raw'], run['timeline'][0])
            (path / 'r12.json').write_text(json.dumps({key: '模型怀疑假设不够强。'}))
            attach_summaries(run, 'case', folder)
            self.assertEqual(run['timeline'][0]['summary'], '模型怀疑假设不够强。')
            other = self.run_data()
            other['raw'][0] = other['raw'][0].replace('weak', 'strong')
            attach_summaries(other, 'case', folder)
            self.assertNotIn('summary', other['timeline'][0])

    def test_source_keeps_text_and_drops_signature_only(self):
        run = self.run_data()
        block = source_step(run, 1)['records'][0]['content'][0]
        self.assertEqual(block['thinking'], 'Maybe the hypothesis is too weak.')
        self.assertNotIn('signature', block)
        self.assertIn('signature', run['raw'][0])

    def test_full_trace_keeps_all_steps_and_long_text(self):
        run = self.run_data()
        event = json.loads(run['raw'][0])
        text = 'Long thought. ' * 10000
        event['message']['content'][0]['thinking'] = text
        run['raw'].append(json.dumps(event))
        run['timeline'].insert(1, {'kind': 'thinking', 'lines': [2]})
        steps = full_trace(run)
        self.assertEqual([step['step'] for step in steps], [1, 2])
        self.assertEqual(steps[1]['records'][0]['content'][0]['thinking'], text)
