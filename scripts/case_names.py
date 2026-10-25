"""Stable benchmark IDs and legacy-name lookup."""
import json
from pathlib import Path

CASES = json.loads((Path(__file__).resolve().parents[1] / 'benchmarks/case-names.json').read_text())
BY_NAME = {case['name']: case for case in CASES}
ALIASES = {alias: case['name'] for case in CASES
           for alias in (case['id'], case['old_name'], case['name'])}


def canonical_name(name):
    name = name.replace('__security-stlc__', '__secure-stlc__')
    return ALIASES.get(name, name)


def case_parts(name):
    """Return task family, difficulty and features, excluding the unique ID."""
    case = BY_NAME.get(canonical_name(name))
    if case is None:
        return None
    features = frozenset() if case['features'] == 'none' else frozenset(case['features'].split('+'))
    return case['language'] + '__' + case['target'], case['difficulty'], features


def difficulty(name):
    parts = case_parts(name)
    return parts[1] if parts else name.rsplit('-', 1)[-1]
