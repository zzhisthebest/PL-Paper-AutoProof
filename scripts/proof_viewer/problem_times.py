"""Validate problem intervals and calculate per-run and per-case time totals."""
import hashlib
import json
from pathlib import Path

CATEGORIES = {
    'lr': 'LR 设计与实现', 'statement': 'Lemma statement 与前提',
    'missing_lemma': '缺少辅助 lemma', 'proof_structure': 'Induction 与证明结构',
    'rewrite': '表达式对应与 rewrite', 'tactic': 'Tactic、solver 与参数',
    'localization': '错误定位', 'tooling': '工具与文件操作',
    'other': '其他明确困难', 'uncertain': '原因尚不能确定',
}


def attach_problem_times(run, case):
    saved = Path(__file__).with_name('problem_analyses') / case / f"r{run['repeat']:02}.json"
    if saved.exists():
        analysis = json.loads(saved.read_text())
        digest = hashlib.sha256(''.join(run['raw']).encode()).hexdigest()
        if analysis.get('trace_sha256') == digest:
            run['problemTimes'] = compile_analysis(run, analysis)
            return
    pilots = json.loads(Path(__file__).with_name('problem_time_pilot.json').read_text())['runs']
    pilot = next((p for p in pilots if p['case'] == case[:3] and p['repeat'] == run['repeat']), None)
    if pilot is None:
        return
    run['problemTimes'] = compile_analysis(run, pilot)


def compile_analysis(run, pilot):

    def interval(a, b):
        assert isinstance(a, int) and isinstance(b, int) and 0 <= a < b <= len(run['timeline']), f'Invalid step interval {a}, {b}'
        start = run['timeline'][a - 1]['elapsedSeconds'] if a else 0
        end = run['timeline'][b - 1]['elapsedSeconds']
        assert start is not None and end is not None and 0 <= start <= end <= run['seconds'], f'Missing/out-of-range timestamps at {a}, {b}: {start}, {end}'
        return dict(after=a, through=b, start=start, end=end)

    def ranges_for(item):
        assert item['title'].strip() and item['intervals'], 'Empty title/intervals'
        return [interval(v['after'], v['through']) if isinstance(v, dict) else interval(*v)
                for v in item['intervals']]

    problems, spans = [], []
    for item in pilot['problems']:
        ranges = ranges_for(item)
        evidence = item.get('evidence_lines', [])
        if 'trace_sha256' in pilot:
            assert item.get('category') in CATEGORIES, 'Unknown category'
            assert evidence, 'Problem has no evidence'
            allowed = {line for r in ranges for step in run['timeline'][max(0,r['after']-1):r['through']]
                       for line in step['lines']}
            assert all(isinstance(line, int) and 1 <= line <= len(run['raw']) for line in evidence), 'Invalid evidence line'
            assert any(line in allowed for line in evidence), f'No evidence inside problem interval: {item["title"]}'
        spans.extend((r['start'], r['end']) for r in ranges)
        problems.append(dict(title=item['title'], outcome=item['outcome'], ranges=ranges,
                             seconds=sum(r['end'] - r['start'] for r in ranges),
                             qualification=item.get('qualification', ''),
                             category=item.get('category'), resolution=item.get('resolution'),
                             evidence_lines=evidence))
    spans.sort()
    assert all(a[1] <= b[0] for a, b in zip(spans, spans[1:])), 'Problem intervals overlap'

    other, phase_spans = [], []
    for phase in pilot['phases']:
        remaining = 0
        for r in ranges_for(phase):
            start, end = r['start'], r['end']
            phase_spans.append((start, end))
            covered = sum(max(0, min(end, b) - max(start, a)) for a, b in spans)
            remaining += end - start - covered
        if remaining > .001:
            other.append(dict(title=phase['title'] + '（未单列问题的部分）', seconds=remaining))
    phase_spans.sort()
    assert all(a[1] <= b[0] for a, b in zip(phase_spans, phase_spans[1:]))
    for start, end in spans:
        assert abs(sum(max(0, min(end, b) - max(start, a)) for a, b in phase_spans) - (end-start)) < .001
    unassigned = run['seconds'] - sum(b-a for a, b in phase_spans)
    if unassigned > .001:
        other.append(dict(title='未覆盖区间或计时边界差额', seconds=unassigned))
    total = sum(p['seconds'] for p in problems) + sum(p['seconds'] for p in other)
    assert abs(total - run['seconds']) < .001
    return dict(problems=sorted(problems, key=lambda p: -p['seconds']), other=other,
                summary=pilot.get('summary', ''), analyzed='trace_sha256' in pilot)


def case_overview(runs):
    groups = {}
    analyzed = [r for r in runs if r.get('problemTimes', {}).get('analyzed')]
    for run in analyzed:
        for p in run['problemTimes']['problems']:
            row = groups.setdefault(p['category'], dict(category=p['category'], title=CATEGORIES[p['category']], seconds=0, occurrences=[]))
            row['seconds'] += p['seconds']
            row['occurrences'].append(dict(repeat=run['repeat'], title=p['title'], seconds=p['seconds'],
                                          after=p['ranges'][0]['after'], resolution=p['resolution']))
    for row in groups.values():
        row['runs'] = len({p['repeat'] for p in row['occurrences']})
        row['occurrences'].sort(key=lambda p: -p['seconds'])
    return dict(analyzed=len(analyzed), total=len(runs),
                seconds=sum(r['seconds'] for r in analyzed),
                problemSeconds=sum(p['seconds'] for p in groups.values()),
                categories=sorted(groups.values(), key=lambda p: -p['seconds']))
