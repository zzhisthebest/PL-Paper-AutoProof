"""Audited interpretations of specific trace records; original traces stay intact."""
import json
from pathlib import Path


def apply_review(record, steps, snapshot):
    reviews = json.loads(Path(__file__).with_name('manual_review.json').read_text())
    key = f"{record.get('case', '')[:3]}/r{record['repeat']:02}"
    review = reviews.get(key, {})
    by_line = {step.get('traceLine'): step for step in steps}
    for line, correction in review.get('steps', {}).items():
        step = by_line[int(line)]
        command = step['input'].get('command', '')
        assert correction['contains'] in command, (key, line, 'trace changed')
        if 'replay' in correction:
            step['reviewedCommand'] = correction['replay']
        if 'keep_before' in correction:
            assert correction['keep_before'] in command
            step['reviewedCommand'] = command.split(correction['keep_before'], 1)[0]
        for old, new in correction.get('replace', []):
            current = step.get('reviewedCommand', command)
            assert old in current, (key, line, 'replacement missing')
            step['reviewedCommand'] = current.replace(old, new, 1)
        if 'preserve' in correction:
            step['reviewedPreserve'] = correction['preserve']
        if 'cwd_after' in correction:
            step['reviewedCwd'] = correction['cwd_after']
        if 'capture' in correction:
            capture = correction['capture']
            text = step['output'].split(capture['start'], 1)[1]
            text = capture['start'] + text
            assert text.rstrip().endswith(capture['end'])
            step.update(file=capture['file'], after=snapshot(text.rstrip('\n') + '\n'))
        step['reviewNote'] = correction['reason']
    return review
