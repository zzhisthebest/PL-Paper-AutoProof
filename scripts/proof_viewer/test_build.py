import json
import tempfile
import unittest
from pathlib import Path

from build import declarations, parse_run, file_history
from timeline import build_timeline
from blocks import classify, sections


class ViewerTests(unittest.TestCase):
    def test_blocks_preserve_source_and_exclude_original_code(self):
        original = ('Definition atom := nat.\n'
                    'Theorem normalization : True.\nAdmitted.\n')
        final = ('Definition atom := nat.\n'
                 '(* Nested (* comment *) before the lemma. *)\n'
                 'Lemma subst_id : True.\nProof.\n  exact I. (* explanation *)\nQed.\n'
                 'Ltac contra_value := idtac "not a period. nor Qed.".\n'
                 'Theorem normalization : True.\nProof.\n  exact I.\nQed.\n'
                 'End Example.\n')
        snapshots = [dict(text=s, declarations=declarations(s)) for s in (original, final)]
        result = classify(dict(snapshots=snapshots, initial=0, final=1))
        by_name = {d['name']: d for d in result}
        self.assertEqual(by_name['atom']['origin'], 'original')
        self.assertEqual(by_name['atom']['addedLines'], 0)
        self.assertEqual(by_name['subst_id']['block'], 'syntax')
        self.assertEqual(by_name['subst_id']['addedLines'], 4)
        self.assertEqual(by_name['normalization']['origin'], 'modified')
        self.assertEqual(by_name['normalization']['addedLines'], 3)
        self.assertEqual(by_name['contra_value']['block'], 'operational')
        self.assertEqual(by_name['contra_value']['end'], 7)
        self.assertEqual(by_name['normalization']['end'], 11)
        self.assertEqual(snapshots[1]['text'], final)

    def test_mutual_definition_stays_together_and_unknown_is_visible(self):
        text = ('Fixpoint LR (n : nat) := match n with\n'
                '| 0 => True | S k => VR k end\n'
                'with VR (n : nat) := match n with\n'
                '| 0 => True | S k => LR k end.\n'
                'Lemma unfamiliar : True.\nProof. exact I. Qed.\n')
        snapshot = dict(text=text, declarations=declarations(text))
        ds = sections(snapshot)
        self.assertEqual(ds[0]['end'], 4)
        result = classify(dict(snapshots=[dict(text='', declarations=[]), snapshot], initial=0, final=1))
        self.assertEqual([d['block'] for d in result], ['lr', 'unknown'])

    def test_timeline_lossless_and_interleaved(self):
        events = [
            {'type': 'system', 'subtype': 'init'},
            {'type': 'assistant', 'message': {'content': [{'type': 'tool_use', 'id': 'a', 'name': 'Bash', 'input': {'command': 'sleep 1'}}]}},
            {'type': 'assistant', 'message': {'content': [{'type': 'thinking', 'thinking': 'Recorded thought'}]}},
            {'type': 'tool_progress', 'tool_use_id': 'a', 'elapsed_time_seconds': 1},
            {'type': 'user', 'message': {'content': [{'type': 'tool_result', 'tool_use_id': 'a', 'content': 'done'}]}},
            {'type': 'result', 'subtype': 'success'},
            {'type': 'new_event', 'unknown_field': {'keep': True}},
            {'type': 'assistant', 'message': {'content': [{'type': 'tool_use', 'id': 'pending', 'name': 'Read', 'input': {}}]}},
        ]
        raw = [json.dumps(e)+'\n' for e in events]
        timeline = build_timeline(raw, [{'traceLine': 5}])
        self.assertEqual(sorted(n for g in timeline for n in g['lines']), list(range(1, 9)))
        call = next(g for g in timeline if g['lines'][0] == 2)
        self.assertEqual(call['lines'], [2, 4, 5])
        self.assertEqual(call['interleaved'], 1)
        self.assertTrue(call['returned'])
        self.assertEqual(timeline[1]['kind'], 'thinking')
        self.assertEqual(timeline[2], call)
        self.assertFalse(timeline[-1]['returned'])
        self.assertEqual([json.loads(x) for x in raw], events)

    def test_history_is_one_file_and_preserves_gaps(self):
        def step(file, before, after):
            return dict(file=file, before=before, after=after, time=1)
        steps = [step('/workspace/Task.v', None, 0),
                 step('/tmp/draft.v', 0, 7),
                 step('/workspace/Task.v', 1, 2),
                 step('/workspace/Task.v', None, 2),
                 step('/workspace/Task.v', None, 3)]
        h = file_history(steps, 0, 3)
        self.assertEqual([v['after'] for v in h], [0, 1, 2, 3])
        self.assertEqual([v['gap'] for v in h], [False, True, False, True])
        self.assertTrue(h[-1]['final'])
        for previous, current in zip(h, h[1:]):
            self.assertEqual(previous['after'], current['before'])

    def test_declarations_ignore_comments_and_strings(self):
        text = '(* Lemma fake : True. (* nested *) *)\nDefinition s := "Lemma nope".\nLemma real : True.\n'
        self.assertEqual([(d['name'], d['line']) for d in declarations(text)], [('s', 2), ('real', 3)])

    def test_replay_and_missing_shell_snapshot(self):
        original = 'Lemma a : True.\nProof.\nQed.\n'
        final = original.replace('Proof.', 'Proof. exact I.')
        events = []

        def tool(name, args, result, error=False):
            tid = str(len(events))
            events.extend([
                {'type': 'assistant', 'timestamp': '2026-10-23T00:00:00Z', 'message': {'content': [
                    {'type': 'tool_use', 'id': tid, 'name': name, 'input': args}]}},
                {'type': 'user', 'timestamp': '2026-10-23T00:00:01Z', 'message': {'content': [
                    {'type': 'tool_result', 'tool_use_id': tid, 'is_error': error, 'content': ''}]},
                 'tool_use_result': result}])

        tool('Read', {}, {'file': {'filePath': '/workspace/Task.v', 'content': original,
                                  'startLine': 1, 'numLines': 3, 'totalLines': 3}})
        tool('Bash', {'command': 'python change.py; rocq c Task.v'}, {'stdout': 'Error: example', 'stderr': ''})
        tool('Edit', {}, {'filePath': '/workspace/Task.v', 'originalFile': original,
                          'oldString': 'Proof.', 'newString': 'Proof. exact I.', 'replaceAll': False})
        tool('Write', {}, {'filePath': '/tmp/scratch.v', 'originalFile': None, 'content': 'Lemma scratch : True.'})
        with tempfile.TemporaryDirectory() as temp:
            trace, proof = Path(temp)/'trace.jsonl', Path(temp)/'Task.v'
            trace.write_text('\n'.join(json.dumps(e) for e in events))
            proof.write_text(final)
            r = parse_run(trace, proof, {'repeat': 1, 'status': 'proved', 'time_s': 10})
        self.assertEqual(r['snapshots'][r['initial']]['text'], original)
        self.assertIsNone(r['steps'][1]['after'])
        self.assertEqual(r['steps'][1]['kind'], 'compile')
        self.assertEqual(r['snapshots'][r['steps'][2]['after']]['text'], final)
        self.assertEqual(r['steps'][3]['file'], '/tmp/scratch.v')
        self.assertEqual(r['steps'][-1]['previous'], r['final'])
        self.assertEqual(r['raw'], [json.dumps(e)+'\n' for e in events[:-1]]+[json.dumps(events[-1])])
        self.assertEqual(sorted(n for g in r['timeline'] for n in g['lines']), list(range(1, len(events)+1)))


if __name__ == '__main__':
    unittest.main()
