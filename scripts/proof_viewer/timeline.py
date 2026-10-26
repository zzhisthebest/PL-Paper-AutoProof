"""Lossless grouping of trace records. No semantic summaries or model calls."""
import json


def build_timeline(raw, steps):
    groups, calls = [], {}
    for number, line in enumerate(raw, 1):
        event = json.loads(line)
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
        covered.extend(group['lines'])
    assert sorted(covered) == list(range(1, len(raw) + 1)), 'Trace records lost or duplicated'
    return groups
