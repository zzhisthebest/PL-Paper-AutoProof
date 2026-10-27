"""Read one original step in character pages, preserving long thinking text."""
import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--step', type=int, required=True)
parser.add_argument('--offset', type=int, default=0)
parser.add_argument('--size', type=int, default=16000)
args = parser.parse_args()
rows = json.loads(Path('full_trace.json').read_text())['steps']
step = next(x for x in rows if x['step'] == args.step)
text = json.dumps(step, ensure_ascii=False, indent=2)
end = min(args.offset + args.size, len(text))
print(f'Step {args.step}: characters [{args.offset}, {end}) of {len(text)}')
print(text[args.offset:end])
print('END_OF_STEP' if end == len(text) else f'next_offset: {end}')
