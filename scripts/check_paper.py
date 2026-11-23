#!/usr/bin/env python3
"""Check proof-map anchors and bind the reviewed manuscript to its sources.

This checks evidence identity. Mathematical fidelity of prose requires the
manual review recorded in paper/PROOF-MAP.json.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lean_anchors  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verified-types', action='store_true',
                        help='also require the successful full public type/axiom receipt')
    args = parser.parse_args()
    record = json.loads((ROOT / 'paper/PROOF-MAP.json').read_text())
    contract = json.loads((ROOT / 'verification/public-contract.json').read_text())
    names = {d['name'] for d in contract['declarations']}
    for file, expected in record['paper_sha256'].items():
        assert digest(ROOT / file) == expected, f'Manuscript changed after route review: {file}'
    tex = '\n'.join((ROOT / file).read_text() for file in record['paper_sha256'])
    bibliography = re.findall(r'\\bibitem\{([^}]+)\}', tex)
    cited = {key.strip() for group in re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}', tex)
             for key in group.split(',')}
    assert len(bibliography) == len(set(bibliography)), 'Duplicate bibliography keys'
    assert cited == set(bibliography), 'Missing or unused bibliography entries'
    count = 0
    for step in record['steps']:
        assert (ROOT / step['section']).is_file()
        for declaration in step['declarations']:
            file = lean_anchors.source_root(declaration, ROOT) / declaration['file']
            assert digest(file) == declaration['source_sha256'], f'Stale proof source: {file}'
            line = file.read_text().splitlines()[declaration['line'] - 1]
            short = re.escape(declaration['name'].rsplit('.', 1)[-1])
            assert re.search(r'\b(?:theorem|lemma|def|abbrev|structure)\s+(?:[\w.]+\.)?' + short + r'\b', line), declaration
            assert declaration['name'] in names, f'Declaration outside public contract: {declaration}'
            count += 1
    if args.verified_types:
        verified = json.loads((ROOT / '.scratch/verification-status.json').read_text())
        assert verified['status'] == 'PASS'
        assert verified['preserved_public_types'] == len(names)
        for file, expected in verified['source_sha256'].items():
            assert digest(ROOT / file) == expected, f'Source changed after type audit: {file}'
        for file, expected in verified['entry_point_sha256'].items():
            assert digest(ROOT / file) == expected, f'Entry point changed after type audit: {file}'
    result = {'status': 'PASS', 'scope': 'Proof-map identity and public-contract coverage',
              'manually_reviewed_steps': len(record['steps']), 'lean_anchors': count,
              'cited_references': len(bibliography),
              'current_full_type_audit_required': args.verified_types,
              'paper_pdf_sha256': digest(ROOT / 'output/pdf/fubini-theorems.pdf')}
    print(json.dumps(result))


if __name__ == '__main__':
    main()
