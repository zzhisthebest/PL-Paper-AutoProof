"""Follow recorded .v files without executing commands from the trace."""
import posixpath
import re
from shell_replay import replay, command_contexts, resolve_path, Unknown

TASK = '/workspace/Task.v'
ERROR = re.compile(r'File "([^"]+\.v)", line (\d+)')


def resolve(path, cwd):
    try:
        return resolve_path(path, cwd)
    except Unknown:
        return None


def shell_files(step, cwd='/workspace'):
    try:
        commands, final_cwd = command_contexts(step['input'].get('command', ''), cwd)
    except (Unknown, ValueError):
        commands, final_cwd = [], cwd
    compiles, candidates = [], []
    for words, _, _, location in commands:
        if words and words[0] in ('echo', 'printf', 'find', 'pkill', 'kill'):
            continue  # A printed command is not a source filename.
        refs = [p for w in words if w.endswith('.v') and '\n' not in w and not w.startswith('^')
                if (p := resolve(w, location))]
        candidates.extend(refs)
        if words and (words[0] in ('coqc', 'coqtop') or words[:2] in (['rocq', 'compile'], ['rocq', 'c'])):
            compiles.extend(refs)
    errors = []
    for path, line in ERROR.findall(step['output']):
        matches = set(p for p in compiles if posixpath.basename(p) == posixpath.basename(path))
        if posixpath.isabs(path):
            resolved = resolve(path, final_cwd)
        elif len(matches) == 1:
            resolved = matches.pop()
        elif len(matches) > 1:
            continue  # Same filename compiled in multiple directories: ambiguous.
        else:
            resolved = resolve(path, final_cwd)
        if resolved:
            errors.append(dict(path=resolved, line=int(line)))
    paths = list(dict.fromkeys([e['path'] for e in errors] + (compiles or candidates)))
    return paths, errors


def next_cwd(step, cwd):
    output = step['output']
    if 'reviewedCwd' in step:
        return step['reviewedCwd']
    if 'Shell syntax error before first command' in step.get('shellIssues', []):
        return cwd
    background = re.search(r'Session cwd remains ([^;\n]+);', step.get('cwdHint', '') + output)
    if background:
        return resolve(background[1].strip(), cwd)
    reset = re.search(r'Shell cwd was reset to ([^\r\n]+)', output)
    if reset:
        return resolve(reset[1].strip(), cwd)
    if re.search(r'(?:bash:|cd:).*?(?:No such file|Not a directory|Permission denied)', output):
        return cwd
    try:
        return command_contexts(step['input'].get('command', ''), cwd)[1]
    except (Unknown, ValueError):
        return None


def may_write(command):
    """Conservative: a script/edit/redirection can invalidate cached contents."""
    return bool(re.search(r'\b(?:python\d*|perl|ruby|node|cp|mv|rm|tee|patch|touch)\b|'
                          r'\bsed\s+[^\n]*-[^\s]*i|(?<![\d])\s>{1,2}\s*[^&]', command))


def attach_files(timeline, steps, snapshots=None, snapshot=None, review=None):
    files = {}
    virtual = {}
    cwd = '/workspace'
    active = TASK
    initial_untouched = True
    review = review or {}
    for item in timeline:
        step = steps[item['step']] if item['step'] is not None else None
        errors = []
        paths = []
        recovered = {}
        shell_before = {}
        if step and step['tool'] == 'Bash':
            if may_write(step['input'].get('command', '')):
                initial_untouched = False
            paths, errors = shell_files(step, cwd)
            paths = [p for p in paths if p not in review.get('ignore_files', {})]
            if snapshot is not None:
                shell_before = {p: dict(f) for p, f in files.items()}
                recorded = {}
                removed = set()
                preserved = {p: virtual[p] for p in step.get('reviewedPreserve', []) if p in virtual}
                virtual, changes, issues = replay(step.get('reviewedCommand', step['input'].get('command', '')), virtual, recorded, cwd=cwd, output=step['output'], removed=removed)
                virtual.update(preserved)
                exit_match = re.search(r'^Exit code (\d+)\s*$', step['output'], re.M)
                interrupted = exit_match is not None and int(exit_match[1]) >= 128
                if interrupted or re.search(r'Traceback \(most recent|Permission denied|No such file or directory|(?:/bin/)?bash:.*syntax error', step['output']):
                    # Execution failure can invalidate reconstructed writes,
                    # but cannot by itself change untouched input files.
                    for path in changes:
                        virtual.pop(path, None)
                    issues.append('命令输出报告执行错误，不能确认写入完成')
                # A later unsupported command invalidates the current state,
                # not the evidence of a write already reconstructed above it.
                for path, text in (recorded | virtual).items():
                    if path.endswith('.v'):
                        sid = snapshot(text)
                        old = files.get(path)
                        if not old or old['stale'] or old['snapshot'] != sid:
                            recovered[path] = dict(path=path, snapshot=sid, snapshotLine=item['end'],
                                                   stale=path not in virtual, partial=None)
                for path, f in files.items():
                    if path not in virtual and any(path == root or path.startswith(root.rstrip('/') + '/') for root in removed):
                        f['deleted'] = True
                        # Keep the historical snapshot and its previous certainty.
                    elif path not in virtual and not f.get('deleted'):
                        f['stale'] = True
                step['shellIssues'] = issues
                step['note'] = '根据 Shell 命令在内存中还原文件；未执行原命令。' if recovered else ''
                if issues:
                    step['note'] += '部分操作无法还原；对应旧快照不再视为当前完整版本。'
                if step.get('reviewNote'):
                    step['note'] += ' 人工核对：' + step['reviewNote']
                if not errors and changes:
                    paths = list(dict.fromkeys([p for p in changes if p.endswith('.v')] + paths))
            elif may_write(step['input'].get('command', '')):
                # We do not guess the effects of arbitrary scripts. A later
                # full Read/Edit/Write supplies the next confirmed snapshot.
                for f in files.values():
                    f['stale'] = True
            cwd = next_cwd(step, cwd)
            if paths:
                active = paths[0]
                for path in paths:
                    files.setdefault(path, dict(path=path, snapshot=None, snapshotLine=None,
                                               stale=False, partial=None))
        elif step and step.get('file', '').endswith('.v'):
            active = step['file']
            # The experiment harness creates Task.v and Task.v.orig from the
            # same input. Seed the backup only from an untouched initial Read,
            # never from a later/final proof or today's benchmark input.
            if (initial_untouched and step['tool'] == 'Read' and active == TASK
                    and step['after'] is not None and snapshots is not None):
                virtual.setdefault(TASK + '.orig', snapshots[step['after']]['text'])
            if step['tool'] in ('Write', 'Edit'):
                initial_untouched = False

        old = files.get(active, dict(path=active, snapshot=None, snapshotLine=None,
                                     stale=False, partial=None))
        if active in shell_before:
            old = shell_before[active]
        item.update(priorSnapshot=old['snapshot'], before=None, after=None,
                    gap=False, gapBefore=False, exact=False, changed=False)
        if recovered:
            files.update(recovered)
        if active in recovered:
            item.update(before=old['snapshot'], after=recovered[active]['snapshot'],
                        exact=old['snapshot'] is not None and not old['stale'],
                        changed=old['snapshot'] != recovered[active]['snapshot'],
                        gapBefore=old['stale'] and old['snapshot'] is not None)
        elif step and step.get('file') == active and step['after'] is not None:
            if snapshots is not None and active in virtual:
                expected = step['before'] if step['before'] is not None else step['after']
                step['replayCheck'] = virtual[active].rstrip('\n') == snapshots[expected]['text'].rstrip('\n')
            item['before'] = step['before'] if step['before'] is not None else old['snapshot']
            item['after'] = step['after']
            item['gap'] = step['before'] is None and old['snapshot'] is not None and old['snapshot'] != step['after']
            item['gapBefore'] = step['before'] is not None and old['snapshot'] is not None and old['snapshot'] != step['before']
            item['exact'] = step['before'] is not None
            item['changed'] = item['before'] is not None and item['before'] != item['after']
            files[active] = dict(path=active, snapshot=step['after'], snapshotLine=item['end'],
                                 stale=False, partial=None)
            if snapshots is not None:
                virtual[active] = snapshots[step['after']]['text']
        elif step and step.get('file') == active and step.get('partial'):
            partial = step['partial']
            start = partial['start'] - 1
            lines = partial['text'].splitlines()
            consistent = (active in virtual and
                          virtual[active].splitlines()[start:start + len(lines)] == lines)
            if not consistent:
                files[active] = dict(old, partial=dict(partial, traceLine=item['end']), stale=True)
                virtual.pop(active, None)
        else:
            files.setdefault(active, old)

        item['file'] = active
        for path, reason in review.get('unavailable', {}).items():
            if path in files and files[path]['snapshot'] is None:
                files[path]['unavailableReason'] = reason
        item['files'] = [dict(f) for f in files.values()]
        item['errors'] = errors
        current = files[active]
        item['snapshot'], item['snapshotLine'] = current['snapshot'], current['snapshotLine']
