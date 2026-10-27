"""Lossless grouping of trace records. No semantic summaries or model calls."""
import json
from datetime import datetime, timedelta


def step_duration(group, records):
    """Use recorded thinking time or paired tool timestamps, never unrelated gaps."""
    first = records[group['lines'][0] - 1]
    if group['kind'] == 'thinking':
        milliseconds = first.get('thinking_duration_ms')
        if isinstance(milliseconds, (int, float)) and milliseconds >= 0:
            return milliseconds / 1000
    if group['kind'] == 'tool' and group['returned']:
        results = [records[n - 1] for n in group['lines']
                   if any(b.get('type') == 'tool_result'
                          for b in records[n - 1].get('message', {}).get('content', [])
                          if isinstance(b, dict))]
        if results and first.get('timestamp') and results[-1].get('timestamp'):
            start = datetime.fromisoformat(first['timestamp'].replace('Z', '+00:00'))
            end = datetime.fromisoformat(results[-1]['timestamp'].replace('Z', '+00:00'))
            seconds = (end - start).total_seconds()
            if seconds >= 0:
                return seconds
    return None


def build_timeline(raw, steps):
    groups, calls = [], {}
    records = [json.loads(line) for line in raw]
    first_timed = next((r for r in records if r.get('timestamp')), None)
    origin = None
    if first_timed:
        origin = datetime.fromisoformat(first_timed['timestamp'].replace('Z', '+00:00'))
        origin -= timedelta(milliseconds=first_timed.get('thinking_duration_ms', 0) or 0)
    for number, event in enumerate(records, 1):
        content = event.get('message', {}).get('content', [])
        blocks = content if isinstance(content, list) else []
        uses = [b for b in blocks if isinstance(b, dict) and b.get('type') == 'tool_use']
        results = [b for b in blocks if isinstance(b, dict) and b.get('type') == 'tool_result']
        key = None
        if len(results) == 1:
            key = (event.get('session_id'), results[0].get('tool_use_id'))
        elif event.get('type') == 'tool_progress':
            key = (event.get('session_id'), event.get('tool_use_id'))
        if key is not None and key in calls:
            group = calls[key]
            group['lines'].append(number)
            if results:
                group['returned'] = True
            continue
        kind = event.get('type', 'unknown')
        label = event.get('subtype') or kind
        if len(uses) == 1:
            kind, label = 'tool', uses[0].get('name', '工具')
        elif kind == 'assistant':
            kinds = {b.get('type') for b in blocks if isinstance(b, dict)}
            if kinds == {'thinking'}:
                kind, label = 'thinking', '模型思考'
            elif kinds == {'text'}:
                kind, label = 'text', '模型回复'
            else:
                kind, label = 'message', '模型消息'
        elif kind == 'user':
            label = '输入消息 / 工具返回'
        elif kind == 'result':
            label = '本轮运行结束'
        elif kind == 'system':
            label = '系统事件 · ' + label
        group = dict(kind=kind, label=label, lines=[number], returned=False)
        groups.append(group)
        if len(uses) == 1:
            calls[(event.get('session_id'), uses[0]['id'])] = group

    # A merged operation is placed at its last record, not at its start:
    # intervening thoughts retain their position before the operation completes.
    groups.sort(key=lambda g: g['lines'][-1])
    tool_steps = {s['traceLine']: i for i, s in enumerate(steps) if s.get('traceLine')}
    covered = []
    for group in groups:
        group['start'], group['end'] = group['lines'][0], group['lines'][-1]
        group['interleaved'] = group['end'] - group['start'] + 1 - len(group['lines'])
        group['step'] = next((tool_steps[n] for n in reversed(group['lines']) if n in tool_steps), None)
        group['durationSeconds'] = step_duration(group, records)
        stamp = records[group['end'] - 1].get('timestamp')
        group['elapsedSeconds'] = None
        if origin is not None and stamp:
            end = datetime.fromisoformat(stamp.replace('Z', '+00:00'))
            group['elapsedSeconds'] = max(0, (end - origin).total_seconds())
        covered.extend(group['lines'])
    assert sorted(covered) == list(range(1, len(raw) + 1)), 'Trace records lost or duplicated'
    return groups
