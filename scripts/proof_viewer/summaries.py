"""Attach separately written summaries only when the source records match."""
import hashlib
import json
from pathlib import Path


def event_key(raw, event):
    records = '\n'.join(raw[n - 1] for n in event['lines'])
    return hashlib.sha256(records.encode()).hexdigest()


def attach_summaries(run, case, directory=None):
    directory = Path(directory) if directory else Path(__file__).with_name('summaries')
    path = directory / case / f"r{run['repeat']:02}.json"
    if not path.exists():
        return
    summaries = json.loads(path.read_text())
    for event in run['timeline']:
        text = summaries.get(event_key(run['raw'], event))
        if text:
            event['summary'] = text
