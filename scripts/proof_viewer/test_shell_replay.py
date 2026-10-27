import unittest
from shell_replay import replay, sed_edit


class ShellReplayTests(unittest.TestCase):
    def test_unparsed_first_command_does_not_change_files(self):
        known = {'/workspace/a.v':'base'}
        files, _, issues = replay("echo 'unterminated > a.v", known,
                                  output='unexpected EOF while looking for matching quote')
        self.assertEqual(files, known)
        self.assertEqual(issues, ['Shell syntax error before first command'])

    def test_loop_output_redirection(self):
        files, _, issues = replay('cd /tmp && for n in one two; do echo "Check $n."; done > out.v', {})
        self.assertFalse(issues)
        self.assertEqual(files['/tmp/out.v'], 'Check one.\nCheck two.\n')

    def test_head_filter_pipelines(self):
        known = {'/workspace/a.v':'one\ntwo\nthree\n'}
        files, _, issues = replay("head -2 a.v | tail -1 > b.v; head -2 a.v | sed 's/one/new/' > c.v", known)
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/b.v'], 'two\n')
        self.assertEqual(files['/workspace/c.v'], 'new\ntwo\n')

    def test_wrapped_inspection_shell(self):
        known = {'/workspace/a.v':'base'}
        files, _, issues = replay("timeout 60 bash -c 'echo Check. | coqtop -quiet' 2>&1 | head -20", known)
        self.assertFalse(issues)
        self.assertEqual(files, known)

    def test_parenthesized_concatenation(self):
        files, _, issues = replay('(echo "Set Printing All."; cat part2.v) > part3.v',
                                  {'/workspace/part2.v':'original'})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/part3.v'], 'Set Printing All.\noriginal')

    def test_python_shared_edit_function_and_delete(self):
        cmd = "python3 - <<'PY'\ns=open('a.v').read()\ndef patch(old,new):\n global s\n s=s.replace(old,new)\npatch('old','new')\nlines=s.splitlines(True)\ndel lines[1:2]\nopen('a.v','w').write(''.join(lines))\nPY"
        files, _, issues = replay(cmd, {'/workspace/a.v': 'old\nremove\n'})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/a.v'], 'new\n')

    def test_comprehension_and_fstring(self):
        cmd = "python3 - <<'PY'\nxs=[f'{i}' for i in range(4) if i > 1]\nopen('a.v','w').write(''.join(xs))\nPY"
        files, _, issues = replay(cmd, {})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/a.v'], '23')

    def test_timed_compiler_preserves_sources(self):
        known = {'/workspace/a.v': 'base'}
        files, _, issues = replay('time timeout 100 rocq compile a.v | head -20', known)
        self.assertEqual(files, known)
        self.assertFalse(issues)

    def test_delete_known_glob_and_sed_relative_range(self):
        files, _, issues = replay('rm /tmp/probe*.v', {'/tmp/probe1.v':'a','/workspace/Task.v':'b'})
        self.assertFalse(issues)
        self.assertEqual(files, {'/workspace/Task.v':'b'})
        self.assertEqual(sed_edit('a\nmarker\nx\ny\nz\n', '/marker/,+2d'), 'a\nz\n')

    def test_python_compiled_regex(self):
        cmd = "python3 -c \"import re; p=re.compile('old'); s,n=p.subn('new',open('a.v').read()); open('a.v','w').write(s)\""
        files, _, issues = replay(cmd, {'/workspace/a.v': 'old'})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/a.v'], 'new')

    def test_python_explicit_exit_preserves_source(self):
        files, _, issues = replay("python3 -c 'raise SystemExit(1)'", {'/workspace/a.v': 'base'})
        self.assertEqual(files, {'/workspace/a.v': 'base'})
        self.assertTrue(issues)

    def test_python_dict_edit_assertion_stops_before_write(self):
        cmd = "python3 - <<'PY'\ns=open('a.v').read()\nfor n,v in {1:'x',2:'y'}.items():\n assert n == 1\n s += v\nopen('a.v','w').write(s)\nPY"
        files, _, issues = replay(cmd, {'/workspace/a.v': 'base'})
        self.assertEqual(files, {'/workspace/a.v': 'base'})
        self.assertTrue(issues)

    def test_read_only_opam_preserves_sources(self):
        known = {'/workspace/Task.v': 'base'}
        files, _, issues = replay('opam list 2>/dev/null | grep Equations', known)
        self.assertEqual(files, known)
        self.assertFalse(issues)

    def test_python_assembly_argv(self):
        known = {'/workspace/a.v': 'a', '/workspace/b.v': 'b',
                 '/workspace/assemble.py': "import sys\nparts=[]\nfor fn in sys.argv[1:]:\n parts.append(open(fn).read())\nopen('out.v','w').write(''.join(parts))\n"}
        files, _, issues = replay('python3 assemble.py a.v b.v', known)
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/out.v'], 'ab')

    def test_python_failed_search_preserves_source(self):
        known = {'/workspace/Task.v': 'base'}
        files, _, issues = replay("python3 -c \"s=open('Task.v').read(); i=s.index('absent'); open('Task.v','w').write(s[:i])\"", known)
        self.assertEqual(files, known)
        self.assertTrue(issues)

    def test_python_loop_control(self):
        source = "s=''\nfor i in range(8):\n if i == 1: continue\n if i >= 4: break\n if i > 0 and i < 4: s += str(i)\n pass\nopen('out.v','w').write(s)\n"
        files, _, issues = replay("python3 - <<'PY'\n" + source + 'PY', {})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/out.v'], '23')

    def test_embedded_loop_with_seq_and_heredoc(self):
        command = "echo start; for i in $(seq 1 3); do cat >> out.v <<'EOF'\nQed.\nEOF\ndone"
        files, _, issues = replay(command, {'/workspace/out.v': ''})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/out.v'], 'Qed.\n' * 3)

    def test_awk_prefix_and_sed_stdout(self):
        files, _, issues = replay("awk '/^Theorem/{exit} {print}' a.v > head.v; sed 's/^Qed\\.$/Admitted./' a.v > b.v", {'/workspace/a.v': 'Definition x.\nTheorem t.\nQed.\n'})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/head.v'], 'Definition x.\n')
        self.assertEqual(files['/workspace/b.v'], 'Definition x.\nTheorem t.\nAdmitted.\n')
        self.assertEqual(sed_edit('Check V.\nbase\nPrint V.\n', '/Check V/d; /Print V/d'), 'base\n')

    def test_group_concatenation_and_grep_line_number(self):
        known = {'/workspace/base.v': 'prefix\nTheorem t.\nold\n', '/workspace/body.v': 'new\n'}
        command = 'n=$(grep -n "^Theorem" base.v | cut -d: -f1) && { head -n $((n-1)) base.v; cat body.v; echo End.; } > out.v'
        files, _, issues = replay(command, known)
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/out.v'], 'prefix\nnew\nEnd.\n')

    def test_shell_group_text_inside_heredoc_is_literal(self):
        files, _, issues = replay("cat > a.v <<'EOF'\n{ echo x; cat y; } > z\nEOF", {})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/a.v'], '{ echo x; cat y; } > z\n')

    def test_end_of_input_terminates_heredoc(self):
        files, _, issues = replay("cat > a.v <<'EOF'\nunfinished\n", {})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/a.v'], 'unfinished\n')

    def test_compiler_output_redirection_only_invalidates_output(self):
        files, _, issues = replay('coqtop < a.v > out.txt', {'/workspace/a.v': 'code'})
        self.assertTrue(issues)
        self.assertEqual(files['/workspace/a.v'], 'code')

    def test_unresolved_read_only_assignment_preserves_inputs(self):
        known = {'/workspace/Task.v': 'base'}
        files, _, issues = replay('n=$(grep -n Theorem Task.v | cut -d: -f1)', known)
        self.assertTrue(issues)
        self.assertEqual(files, known)

    def test_stderr_redirect_is_not_a_copy_operand(self):
        files, _, issues = replay('cp Task.v /tmp/ 2>/dev/null', {'/workspace/Task.v': 'base'})
        self.assertFalse(issues)
        self.assertEqual(files['/tmp/Task.v'], 'base')

    def test_recorded_shell_script_is_interpreted(self):
        files, _, issues = replay('./build.sh', {'/workspace/build.sh': 'cat a.v b.v > all.v\ncoqc all.v',
                                               '/workspace/a.v': 'a', '/workspace/b.v': 'b'})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/all.v'], 'ab')

    def test_python_small_function_and_regex(self):
        source = "import re\ndef block(x):\n return x + ' end'\ns=block(open('a.v').read())\ns=re.sub('old', 'new', s)\nopen('b.v','w').write(s)\n"
        files, _, issues = replay('python3 - <<\'PY\'\n' + source + 'PY', {'/workspace/a.v': 'old'})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/b.v'], 'new end')

    def test_sed_range_and_append(self):
        source = 'prefix\nLemma test\nProof.\nQed.\nsuffix\n'
        self.assertEqual(sed_edit(source, '/^Lemma/,/^Qed/d'), 'prefix\nsuffix\n')
        self.assertEqual(sed_edit('a\nb\n', '1a inserted'), 'a\ninserted\nb\n')
        files, _, issues = replay("sed -n '/^Lemma/,/^Qed/p' a.v > b.v", {'/workspace/a.v': source})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/b.v'], 'Lemma test\nProof.\nQed.\n')

    def test_multiline_python_argument(self):
        files, _, issues = replay('python3 -c "\ns=open(\'base.v\').read()\nopen(\'out.v\',\'w\').write(s)\n"', {'/workspace/base.v': 'base'})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/out.v'], 'base')

    def test_occurrence_report_does_not_modify_sources(self):
        known = {'/workspace/Task.v': 'base'}
        cmd = 'for n in foo bar; do c=$(grep -o "$n" Task.v | wc -l); if [ "$c" -lt 2 ]; then echo "$n"; fi; done; wc -l Task.v'
        files, _, issues = replay(cmd, known)
        self.assertEqual(files, known)
        self.assertFalse(issues)

    def test_observed_conditional_marker_allows_following_copy(self):
        known = {'/workspace/Task.v': 'base'}
        files, _, issues = replay('coqc Task.v && echo CLEAN_OK && cp Task.v check.v', known, output='CLEAN_OK\n')
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/check.v'], 'base')

    def test_literal_shell_loop(self):
        files, _, issues = replay('for n in one two; do printf "%s" "$n" > test.v; done', {})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/test.v'], 'two')

    def test_conditional_inspection_does_not_discard_inputs(self):
        known = {'/workspace/Task.v': 'old', '/tmp/base.v': 'base'}
        files, _, issues = replay('time coqc Task.v && echo OK && cd /tmp && coqc base.v | head -20', known)
        self.assertEqual(files, known)
        self.assertFalse(issues)

    def test_missing_copy_source_only_invalidates_destination(self):
        files, _, issues = replay('cp missing.v draft.v', {'/workspace/base.v': 'base', '/workspace/draft.v': 'old'})
        self.assertEqual(files, {'/workspace/base.v': 'base'})
        self.assertTrue(issues)

    def test_failed_python_edit_preserves_unrelated_files(self):
        files, _, issues = replay("python3 -c \"p='draft.v'; s=open('missing.v').read(); open(p,'w').write(s)\"",
                                  {'/workspace/base.v': 'base', '/workspace/draft.v': 'old'})
        self.assertEqual(files, {'/workspace/base.v': 'base'})
        self.assertTrue(issues)

    def test_saved_python_script_with_loop(self):
        script = "s=open('base.v').read()\nfor a,b in [('one','two'),('two','three')]:\n s=s.replace(a,b)\nwith open('out.v','w') as f:\n f.write(s)\n"
        files, _, issues = replay('python3 edit.py', {'/workspace/edit.py': script, '/workspace/base.v': 'one'})
        self.assertEqual(files['/workspace/out.v'], 'three')
        self.assertFalse(issues)

    def test_conditional_echo_preserves_sources_for_later_drafts(self):
        known = {'/tmp/base.v': 'Definition x := 0.\n'}
        files, _, issues = replay(
            'rocq compile base.v 2>&1 | head -30 && echo BUILD_OK', known, cwd='/tmp')
        self.assertEqual(files, known)
        self.assertFalse(issues)
        files, _, issues = replay(
            "sed -n '1,193p' base.v > t3.v && cat >> t3.v <<'EOF'\nCheck x.\nEOF",
            files, cwd='/tmp')
        self.assertEqual(files['/tmp/t3.v'], known['/tmp/base.v'] + 'Check x.\n')
        self.assertFalse(issues)

    def test_conditional_echo_does_not_unblock_conditional_write(self):
        files, _, issues = replay(
            'coqc Task.v && echo OK && cp Task.v other.v', {'/workspace/Task.v': 'old'})
        self.assertTrue(issues)
        self.assertNotIn('/workspace/other.v', files)

    def test_conditional_echo_redirect_is_not_read_only(self):
        files, _, issues = replay(
            'coqc Task.v && echo changed > Task.v', {'/workspace/Task.v': 'old'})
        self.assertTrue(issues)
        self.assertFalse(files)

    def test_heredoc_then_compile(self):
        files, changed, issues = replay("cd /tmp && cat > check2.v <<'EOF'\nRequire Import dev1.\nPrint Assumptions x.\nEOF\nrocq compile check2.v 2>&1 | head", {})
        self.assertEqual(files['/tmp/check2.v'], 'Require Import dev1.\nPrint Assumptions x.\n')
        self.assertEqual(changed, ['/tmp/check2.v'])
        self.assertEqual(issues, [])

    def test_append_copy_and_head(self):
        files, _, issues = replay("cp Task.v /tmp/a.v\nhead -1 /tmp/a.v > /tmp/b.v\ncat >> /tmp/b.v <<'END'\nnew\nEND", {'/workspace/Task.v': 'one\ntwo\n'})
        self.assertEqual(files['/tmp/b.v'], 'one\nnew\n')
        self.assertEqual(issues, [])

    def test_python_replacement_and_lines(self):
        files, _, issues = replay("python3 - <<'PY'\np='Task.v'\ns=open(p).read()\ns=s.replace('old','new')\nlines=s.splitlines(True)\nlines[1]='last\\n'\nopen(p,'w').write(''.join(lines))\nPY", {'/workspace/Task.v': 'old\nend\n'})
        self.assertEqual(files['/workspace/Task.v'], 'new\nlast\n')
        self.assertFalse(issues)

    def test_unknown_script_cannot_read_host_or_keep_stale_code(self):
        files, _, issues = replay("python3 -c \"import os; os.system('touch /tmp/never-run-this')\"", {'/workspace/Task.v': 'old'})
        self.assertEqual(files, {})
        self.assertTrue(issues)

    def test_dynamic_heredoc_is_not_literal(self):
        files, _, issues = replay('cat > Task.v <<EOF\n$SECRET\nEOF', {})
        self.assertFalse(files)
        self.assertTrue(issues)

    def test_sed_literal_is_linewise(self):
        files, _, issues = replay("sed -i 's/old/new/' Task.v", {'/workspace/Task.v': 'old old\nold\n'})
        self.assertEqual(files['/workspace/Task.v'], 'new old\nnew\n')
        self.assertFalse(issues)

    def test_unknown_then_literal_write_recovers(self):
        files, _, issues = replay("some_script\ncat > /tmp/a.v <<'EOF'\nx\nEOF", {'/tmp/b.v': 'stale'})
        self.assertEqual(files, {'/tmp/a.v': 'x\n'})
        self.assertTrue(issues)

    def test_sed_multiple_replacements(self):
        files, _, issues = replay("sed -i 's/old/new/g; s/first/second/g' Task.v", {'/workspace/Task.v': 'old first'})
        self.assertEqual(files['/workspace/Task.v'], 'new second')
        self.assertFalse(issues)

    def test_unknown_command_keeps_evidence_of_prior_write(self):
        recorded = {}
        files, changed, issues = replay(
            "cd /tmp && cat > trailer.v <<'EOF'\nEnd Example.\nEOF\nchmod +x build.sh && ./build.sh",
            {}, recorded)
        self.assertEqual(recorded, {'/tmp/trailer.v': 'End Example.\n'})
        self.assertEqual(files, {})
        self.assertEqual(changed, ['/tmp/trailer.v'])
        self.assertTrue(issues)

    def test_stale_recorded_text_is_not_used_as_current_input(self):
        recorded = {}
        files, _, _ = replay(
            "cat > a.v <<'EOF'\nold\nEOF\nunknown_script\ncp a.v b.v",
            {}, recorded)
        self.assertEqual(recorded, {'/workspace/a.v': 'old\n'})
        self.assertFalse(files)

    def test_later_full_write_reestablishes_current_version(self):
        recorded = {}
        files, _, _ = replay(
            "cat > a.v <<'EOF'\nold\nEOF\nunknown_script\ncat > a.v <<'EOF'\nnew\nEOF",
            {}, recorded)
        self.assertEqual(files, {'/workspace/a.v': 'new\n'})
        self.assertEqual(recorded, files)

    def test_printf_and_signed_line_counts(self):
        files, _, issues = replay(
            "printf '%s\\n' 'first' 'second' > a.v\nhead -n -1 a.v > b.v\ntail -n +2 a.v > c.v",
            {}, cwd='/workspace/scratch')
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/scratch/a.v'], 'first\nsecond\n')
        self.assertEqual(files['/workspace/scratch/b.v'], 'first\n')
        self.assertEqual(files['/workspace/scratch/c.v'], 'second\n')

    def test_multiple_cd_do_not_relocate_earlier_writes(self):
        files, _, issues = replay("printf 'first' > a.v; cd /tmp; printf 'second' > a.v", {}, cwd='/workspace/scratch')
        self.assertFalse(issues)
        self.assertEqual(files, {'/workspace/scratch/a.v':'first', '/tmp/a.v':'second'})

    def test_group_heredoc_and_multiple_sed_ranges(self):
        files, _, issues = replay("{ echo header; sed -n '1,2p;4,4p' source.v; cat <<'EOF'\nfooter\nEOF\n} > result.v", {'/workspace/source.v': 'a\nb\nc\nd\n'})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/result.v'], 'header\na\nb\nd\nfooter\n')

    def test_python_generator_and_list_index(self):
        files, _, issues = replay("python3 - <<'PY'\ns=open('a.v').read().splitlines()\ni=next(i for i,x in enumerate(s) if x == 'b')\nj=s.index('c')\nopen('b.v','w').write('\\n'.join(s[i:j+1])+'\\n')\nPY", {'/workspace/a.v':'a\nb\nc\n'})
        self.assertFalse(issues)
        self.assertEqual(files['/workspace/b.v'], 'b\nc\n')

    def test_sed_rocq_patterns(self):
        self.assertEqual(sed_edit('apply in_or_app in H.\n', r's/apply in_or_app in H\./apply in_app_or in H./'),
                         'apply in_app_or in H.\n')
        self.assertEqual(sed_edit('a; b\n', 's/a; b/intros; auto/'), 'intros; auto\n')
        self.assertEqual(sed_edit('t\' Hmulti\n', r's/t\x27 Hmulti/t\x27 Hstep/'), "t' Hstep\n")
        self.assertEqual(sed_edit('a\nb\n', '$d'), 'a\n')
        self.assertEqual(sed_edit('a\n', '1i From Stdlib Require Import Lia.'),
                         'From Stdlib Require Import Lia.\na\n')


if __name__ == '__main__':
    unittest.main()
