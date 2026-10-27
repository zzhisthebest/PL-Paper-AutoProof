"""Check every run's final file list in the generated offline viewer."""
import argparse
import base64
import gzip
import json
from pathlib import Path


def audit(html):
    source = html.read_text()
    cases = json.loads(source.split('const CASES=', 1)[1].split(';\nlet DATA', 1)[0])
    rows = []
    for case in cases:
        data = json.loads(gzip.decompress(base64.b64decode(case['data'])))
        for run in data['runs']:
            last = next(event for event in reversed(run['timeline']) if event['kind'] != 'archive')
            for file in last['files']:
                status = (('unavailable' if file.get('unavailableReason') else 'missing') if file['snapshot'] is None else
                          'unconfirmed' if file['stale'] else 'confirmed')
                rows.append(dict(case=case['case'], repeat=run['repeat'],
                                 path=file['path'], status=status,
                                 deleted=file.get('deleted', False),
                                 reason=file.get('unavailableReason', '')))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('html', type=Path)
    parser.add_argument('--output', type=Path, help='Save the file-by-file checklist as JSON')
    args = parser.parse_args()
    rows = audit(args.html)
    print('case  files  missing  unavailable  unconfirmed  confirmed')
    for case in dict.fromkeys(row['case'] for row in rows):
        group = [row for row in rows if row['case'] == case]
        counts = [sum(row['status'] == status for row in group)
                  for status in ('missing', 'unavailable', 'unconfirmed', 'confirmed')]
        print(case.split('__')[0], len(group), *counts)
    print('Total:', len(rows), 'files;', sum(row['deleted'] for row in rows), 'deleted during the run')
    if args.output:
        args.output.write_text(json.dumps(rows, ensure_ascii=False, indent=2) + '\n')


if __name__ == '__main__':
    main()
