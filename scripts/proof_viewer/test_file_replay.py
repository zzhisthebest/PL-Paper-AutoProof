import unittest

from file_replay import attach_files, shell_files, may_write, next_cwd


def operation(tool, file='', before=None, after=None, command='', output='', **extra):
    return dict(tool=tool, file=file, before=before, after=after,
                input={'command': command}, output=output, **extra)


class FileReplayTests(unittest.TestCase):
    def test_initial_read_seeds_harness_backup(self):
        snapshots = [{'text':'original'}]
        steps = [operation('Read', '/workspace/Task.v', after=0),
                 operation('Bash', command='cp Task.v.orig /tmp/probe.v')]
        events = [dict(step=i, end=i+1) for i in range(len(steps))]
        attach_files(events, steps, snapshots, lambda text: 0)
        file = next(f for f in events[-1]['files'] if f['path']=='/tmp/probe.v')
        self.assertEqual(file['snapshot'], 0)
        self.assertFalse(file['stale'])

    def test_background_command_does_not_move_session(self):
        step = operation('Bash', command='cd /tmp && coqtop -l debug.v',
                         cwdHint='Session cwd remains /workspace/work; directory changes made by the backgrounded command do not apply to subsequent commands.')
        self.assertEqual(next_cwd(step, '/workspace/work'), '/workspace/work')

    def test_echo_command_is_not_a_filename(self):
        paths, _ = shell_files(operation('Bash', command='echo "rocq compile b.v"'))
        self.assertEqual(paths, [])

    def test_delete_preserves_confirmed_historical_snapshot(self):
        snapshots = [{'text': 'old\n'}]
        steps = [operation('Read', '/tmp/a.v', after=0), operation('Bash', command='rm -rf /tmp')]
        events = [dict(step=i, end=i+1) for i in range(len(steps))]
        attach_files(events, steps, snapshots, lambda text: 0)
        file = next(f for f in events[-1]['files'] if f['path'] == '/tmp/a.v')
        self.assertTrue(file['deleted'])
        self.assertFalse(file['stale'])
        self.assertEqual(file['snapshot'], 0)

    def test_matching_partial_read_preserves_full_snapshot(self):
        snapshots = [{'text': 'one\ntwo\nthree\n'}]
        steps = [operation('Read', '/workspace/Task.v', after=0),
                 operation('Read', '/workspace/Task.v', partial={'start':2,'text':'two\n'})]
        events = [dict(step=i, end=i+1) for i in range(len(steps))]
        attach_files(events, steps, snapshots, lambda text: 0)
        self.assertFalse(events[-1]['files'][0]['stale'])

    def timeline(self, steps):
        events = [dict(step=i, end=i+1) for i in range(len(steps))]
        attach_files(events, steps)
        return events

    def test_compile_follows_temporary_file_not_task(self):
        steps = [operation('Read', '/workspace/Task.v', after=0),
                 operation('Write', '/tmp/dev1.v', after=1),
                 operation('Bash', command='cd /tmp && rocq compile dev1.v 2>&1 | head -60',
                           output='File "./dev1.v", line 207, characters 25-29:\nError: example')]
        events = self.timeline(steps)
        self.assertEqual(events[-1]['file'], '/tmp/dev1.v')
        self.assertEqual(events[-1]['snapshot'], 1)
        self.assertEqual(events[-1]['errors'], [{'path':'/tmp/dev1.v','line':207}])
        self.assertFalse(events[-1]['files'][-1]['stale'])

    def test_changes_are_compared_with_same_file_only(self):
        steps = [operation('Read', '/workspace/Task.v', after=0),
                 operation('Write', '/tmp/a.v', after=1),
                 operation('Write', '/tmp/b.v', after=2),
                 operation('Edit', '/tmp/a.v', before=1, after=3)]
        events = self.timeline(steps)
        self.assertEqual(events[-1]['priorSnapshot'], 1)
        self.assertEqual(events[-1]['before'], 1)
        self.assertTrue(events[-1]['changed'])
        self.assertFalse(events[-1]['gapBefore'])

    def test_shell_modification_marks_stale_and_no_future_code(self):
        steps = [operation('Read', '/tmp/a.v', after=0),
                 operation('Bash', command="cd /tmp && sed -i 's/a/b/' a.v && coqc a.v",
                           output='File "./a.v", line 42, characters 0-1:'),
                 operation('Read', '/tmp/a.v', after=1)]
        events = self.timeline(steps)
        self.assertFalse(events[0]['files'][0]['stale'])
        self.assertEqual(events[1]['snapshot'], 0)
        self.assertTrue(events[1]['files'][0]['stale'])
        self.assertEqual(events[2]['snapshot'], 1)
        self.assertFalse(events[2]['files'][0]['stale'])

    def test_missing_file_and_partial_read(self):
        steps = [operation('Read', '/workspace/Task.v', after=0),
                 operation('Bash', command='cd /tmp && coqc unknown.v',
                           output='File "./unknown.v", line 207, characters 1-2:'),
                 operation('Read', '/tmp/unknown.v', partial={'start':205,'text':'a\nb\nc'})]
        events = self.timeline(steps)
        self.assertIsNone(events[1]['snapshot'])
        self.assertEqual(events[2]['file'], '/tmp/unknown.v')
        self.assertEqual(events[2]['files'][-1]['partial']['start'], 205)

    def test_plain_compile_is_not_a_source_edit(self):
        self.assertFalse(may_write('cd /tmp && coqc x.v 2>&1 | head -60'))
        self.assertTrue(may_write('python3 fix.py && coqc x.v'))
        paths, _ = shell_files(operation('Bash', command='coqc /tmp/test.v'))
        self.assertEqual(paths, ['/tmp/test.v'])

    def test_shell_snapshot_survives_unsupported_command(self):
        snapshots = []
        def snapshot(text):
            snapshots.append({'text': text})
            return len(snapshots)-1
        steps = [operation('Bash', command="cd /tmp && cat > trailer.v <<'EOF'\nEnd Example.\nEOF\n./build.sh"),
                 operation('Bash', command='cd /tmp && coqc trailer.v')]
        events = [dict(step=i, end=i+1) for i in range(len(steps))]
        attach_files(events, steps, snapshots, snapshot)
        for event in events:
            self.assertEqual(event['file'], '/tmp/trailer.v')
            self.assertEqual(snapshots[event['snapshot']]['text'], 'End Example.\n')
            self.assertTrue(event['files'][0]['stale'])
        self.assertEqual(events[1]['snapshotLine'], 1)

    def test_first_snapshot_after_missing_file_has_no_before_diff(self):
        snapshots = []
        def snapshot(text):
            snapshots.append({'text': text})
            return len(snapshots)-1
        steps = [operation('Bash', command='coqc /tmp/a.v'),
                 operation('Bash', command='unknown_script'),
                 operation('Bash', command="cat > /tmp/a.v <<'EOF'\nnew\nEOF")]
        events = [dict(step=i, end=i+1) for i in range(len(steps))]
        attach_files(events, steps, snapshots, snapshot)
        self.assertIsNone(events[-1]['before'])
        self.assertFalse(events[-1]['gapBefore'])
        self.assertEqual(snapshots[events[-1]['snapshot']]['text'], 'new\n')

    def test_persistent_cwd_and_explicit_reset(self):
        steps = [operation('Bash', command='cd /workspace/scratch && coqc a.v'),
                 operation('Bash', command='coqc b.v'),
                 operation('Bash', command='cd /tmp && coqc c.v', output='Shell cwd was reset to /workspace'),
                 operation('Bash', command='coqc d.v')]
        events = self.timeline(steps)
        self.assertEqual([e['file'] for e in events],
                         ['/workspace/scratch/a.v','/workspace/scratch/b.v','/tmp/c.v','/workspace/d.v'])

    def test_compile_paths_use_cwd_at_each_command(self):
        paths, _ = shell_files(operation('Bash', command='coqc Task.v; cd /tmp && coqc check.v'))
        self.assertEqual(paths, ['/workspace/Task.v','/tmp/check.v'])
        paths, errors = shell_files(operation('Bash', command='coqc Task.v; cd /tmp && coqc check.v',
                                              output='File "./Task.v", line 12, characters 0-1:'))
        self.assertEqual(errors[0]['path'], '/workspace/Task.v')


if __name__ == '__main__':
    unittest.main()
