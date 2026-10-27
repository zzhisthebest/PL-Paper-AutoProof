"""Build an offline proof viewer from saved Claude Code traces. No model calls."""
import argparse
import base64
import difflib
import gzip
import json
import re
from datetime import datetime
from pathlib import Path
from timeline import build_timeline
from blocks import BLOCKS, classify, sections
from functional import DEFINITIONS, infer_labels
from file_replay import attach_files
from manual_review import apply_review
from summaries import attach_summaries
from problem_times import attach_problem_times, case_overview

ROOT = Path(__file__).resolve().parents[2]
DEFAULT = ROOT / 'benchmarkResults/feature_inversion_analysis_20_repeats'
CASE = '001__stlc__strong-normalization__none__hard'
ARCHIVES = [DEFAULT, ROOT / 'benchmarkResults/representative_cases_20_repeats']


def declarations(text):
    # Mask nested Rocq comments and strings, preserving positions and line numbers.
    masked = list(text)
    i, depth, quoted = 0, 0, False
    while i < len(text):
        pair = text[i:i + 2]
        if not quoted and pair == '(*':
            depth += 1
            masked[i:i + 2] = '  '
            i += 2
        elif depth and pair == '*)':
            depth -= 1
            masked[i:i + 2] = '  '
            i += 2
        elif depth:
            if text[i] != '\n':
                masked[i] = ' '
            i += 1
        elif text[i] == '"':
            masked[i] = ' '
            if quoted and pair == '""':
                masked[i + 1] = ' '
                i += 2
            else:
                quoted = not quoted
                i += 1
        else:
            if quoted and text[i] != '\n':
                masked[i] = ' '
            i += 1
    pattern = r'(?m)^\s*(?:(?:Local|Global|Program)\s+)*(Lemma|Theorem|Corollary|Proposition|Definition|Fixpoint|Inductive|Record|Equations)\s+([\w\x27]+)'
    return [dict(kind=m[1], name=m[2], line=text.count('\n', 0, m.start(1)) + 1)
            for m in re.finditer(pattern, ''.join(masked))]


def elapsed(timestamp, start):
    if not timestamp or not start:
        return None
    return round((datetime.fromisoformat(timestamp.replace('Z', '+00:00')) - start).total_seconds(), 1)


def file_history(steps, initial, final_id):
    """One continuous Task.v history. Gaps are separate, never hidden in an Edit."""
    history = [dict(before=None, after=initial, event=0, startEvent=0,
                    exact=False, label='初始题面', time=0, gap=False)]
    current, last_event = initial, 0

    def append(sid, index, exact, label, gap):
        nonlocal current, last_event
        if sid == current:
            return
        history.append(dict(before=current, after=sid, event=index, startEvent=last_event,
                            exact=exact, label=label, time=steps[index]['time'], gap=gap))
        current, last_event = sid, index

    for index, step in enumerate(steps):
        if step.get('file') != '/workspace/Task.v' or step['after'] is None:
            continue
        if step['before'] is not None:
            append(step['before'], index, False, '中间修改未完整记录', True)
            append(step['after'], index, True, '修改 Task.v', False)
        else:
            append(step['after'], index, False, '中间修改未完整记录', True)
    assert current == final_id
    history[-1]['final'] = True
    return history


def parse_run(trace, final, record):
    snapshots, by_text, steps, calls = [], {}, [], {}
    start = None
    initial = None
    observed = {}

    def snapshot(text):
        if text not in by_text:
            by_text[text] = len(snapshots)
            snapshots.append(dict(text=text, declarations=declarations(text)))
        return by_text[text]

    opener = gzip.open if trace.suffix == '.gz' else open
    with opener(trace, 'rt') as stream:
        raw = list(stream)
        for trace_line, line in enumerate(raw, 1):
            if '"tool_use"' not in line and '"tool_use_result"' not in line:
                continue
            event = json.loads(line)
            stamp = event.get('timestamp')
            if start is None and stamp:
                start = datetime.fromisoformat(stamp.replace('Z', '+00:00'))
            content = event.get('message', {}).get('content', [])
            if not isinstance(content, list):
                continue
            if event.get('type') == 'assistant':
                for item in content:
                    if item.get('type') == 'tool_use':
                        calls[item['id']] = (item, stamp)
                continue
            for item in content:
                if item.get('type') != 'tool_result':
                    continue
                call, when = calls.pop(item.get('tool_use_id'), ({}, stamp))
                if not call:
                    continue
                name, args = call.get('name'), call.get('input', {})
                result = event.get('tool_use_result', {})
                failed = bool(item.get('is_error'))
                path = args.get('file_path', '')
                if isinstance(result, dict):
                    path = result.get('filePath', result.get('file', {}).get('filePath', path))
                path = str(Path(path)) if path else ''
                step = dict(tool=name, time=elapsed(when, start), end=elapsed(stamp, start),
                            input=args, output=item.get('content', ''), before=None, after=None,
                            previous=observed.get(path), file=path, kind='tool', label=name, note='', traceLine=trace_line)
                if isinstance(result, dict):
                    if name == 'Bash':
                        command = args.get('command', '')
                        step['kind'] = 'compile' if re.search(r'\b(?:coqc|coqtop|rocq\s+(?:c|compile|top))\b', command) else 'shell'
                        step['label'] = args.get('description') or command.split('\n')[0][:100]
                        step['output'] = result.get('stdout', '') + '\n' + result.get('stderr', '')
                        step['cwdHint'] = result.get('backgroundCwdHint', '')
                        step['note'] = 'Shell 命令没有文件快照；编译输出可能针对草稿文件。请以原命令为准。'
                    elif name == 'Read':
                        file = result.get('file', {})
                        full = (file.get('startLine') == 1 and file.get('numLines') == file.get('totalLines'))
                        if full and path.endswith('.v'):
                            text = file['content']
                            sid = snapshot(text)
                            step.update(after=sid, kind='snapshot', label=f'读取 {Path(path).name} 完整快照')
                            step['output'] = ''
                            if initial is None and Path(path).name == 'Task.v':
                                initial = sid
                            observed[path] = sid
                        else:
                            step['output'] = file.get('content', step['output'])
                            if not failed and path.endswith('.v') and isinstance(file.get('content'), str):
                                step['partial'] = dict(text=file['content'], start=file.get('startLine', 1))
                    elif name == 'Edit' and not failed and path.endswith('.v'):
                        before = result.get('originalFile')
                        old, new = result.get('oldString'), result.get('newString')
                        if isinstance(before, str) and isinstance(old, str) and old and old in before:
                            after = before.replace(old, new, -1 if result.get('replaceAll') else 1)
                            step.update(before=snapshot(before), after=snapshot(after), kind='edit',
                                        label=f'修改 {Path(path).name}', output='')
                            observed[path] = step['after']
                    elif name == 'Write' and not failed and path.endswith('.v'):
                        if isinstance(result.get('content'), str):
                            before = result.get('originalFile')
                            step.update(before=snapshot(before) if isinstance(before, str) else None,
                                        after=snapshot(result['content']), kind='edit', label=f'写入 {Path(path).name}', output='')
                            observed[path] = step['after']
                if failed:
                    step['label'] += '（工具报错）'
                if initial is None and path == '/workspace/Task.v' and step['before'] is not None:
                    initial = step['before']
                if step['after'] is not None and step['before'] is None and step['previous'] is not None:
                    if step['after'] != step['previous']:
                        step['note'] = '与上次完整快照之间有变化；这段差异不能归因于当前读取操作。'
                if step['before'] is not None and step['previous'] is not None and step['before'] != step['previous']:
                    step['note'] = '本次修改前的文件与上次快照不同；中间存在未还原的修改。'
                if not isinstance(step['output'], str):
                    step['output'] = json.dumps(step['output'], ensure_ascii=False, indent=2)
                steps.append(step)

    assert initial is not None, f'No initial full Read in {trace}'
    final_id = snapshot(final.read_text())
    steps.append(dict(tool='Archive', time=record['time_s'], end=record['time_s'], kind='final',
                      label='归档的最终 Task.v', before=None, after=final_id, previous=observed.get('/workspace/Task.v'), file='/workspace/Task.v',
                      input={}, output='', note='这是最终归档文件，不是一次工具调用。'))
    original_lines = snapshots[initial]['text'].splitlines()
    final_lines = snapshots[final_id]['text'].splitlines()
    same_lines = []
    for tag, _, _, j, k in difflib.SequenceMatcher(None, original_lines, final_lines, autojunk=False).get_opcodes():
        if tag == 'equal':
            same_lines.extend(range(j + 1, k + 1))
    timeline = build_timeline(raw, steps)
    timeline.append(dict(kind='archive', label='归档的最终 Task.v', lines=[], start=len(raw)+1,
                         end=len(raw)+1, interleaved=0, step=len(steps)-1, returned=False))
    review = apply_review(record, steps, snapshot)
    attach_files(timeline, steps, snapshots, snapshot, review=review)
    return dict(repeat=record['repeat'], status=record['status'], seconds=record['time_s'],
                initial=initial, final=final_id, snapshots=snapshots, steps=steps,
                history=file_history(steps, initial, final_id), originalLines=same_lines,
                raw=raw, timeline=timeline)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results', type=Path, help='只导出指定结果目录；默认包含两个重复实验目录')
    parser.add_argument('--case', help='只导出指定题目；默认导出所有六题')
    parser.add_argument('--output', type=Path, default=DEFAULT / 'proof-viewer.html')
    args = parser.parse_args()
    cases = []
    for archive in ([args.results] if args.results else ARCHIVES):
        records = json.loads((archive / 'results.json').read_text())
        for case in sorted({r['case'] for r in records}):
            if args.case and case != args.case:
                continue
            runs = []
            for record in sorted(records, key=lambda r: r['repeat']):
                if record['case'] != case:
                    continue
                run = parse_run(archive / record['trace'], archive / record['proof'], record)
                attach_summaries(run, case)
                attach_problem_times(run, case)
                labels = {}
                if case == CASE:
                    labels = None
                elif case[:3] in DEFINITIONS:
                    labels = infer_labels(sections(run['snapshots'][run['final']]), case[:3])
                run['blocks'] = classify(run, labels=labels, alpha=True)
                runs.append(run)
                print(f"{case[:3]} r{record['repeat']:02}: {len(run['steps'])} steps, {len(run['snapshots'])} snapshots", flush=True)
            payload = json.dumps(dict(case=case, runs=runs, blockLabels=BLOCKS, problemOverview=case_overview(runs),
                                      classified=case == CASE or case[:3] in DEFINITIONS, alpha=True),
                                 ensure_ascii=False, separators=(',', ':')).encode()
            # Keep one portable file without inflating all 120 traces at startup.
            packed = base64.b64encode(gzip.compress(payload, mtime=0)).decode('ascii')
            cases.append(dict(case=case, count=len(runs), data=packed))
    assert cases, 'No matching cases'
    data = json.dumps(cases, ensure_ascii=False, separators=(',', ':'))
    data = data.replace('<', '\\u003c').replace('\u2028', '\\u2028').replace('\u2029', '\\u2029')
    template = Path(__file__).with_name('viewer.html').read_text()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(template.replace('/*DATA*/null', data))
    print(f'{args.output} ({args.output.stat().st_size / 1024**2:.1f} MiB)')


if __name__ == '__main__':
    main()
