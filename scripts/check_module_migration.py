#!/usr/bin/env python3
"""Verify that a module port preserves all pre-existing mathematical source.

Imports, module visibility and the two documented compatibility options are
checked separately from the normalized source body. Full Lean type/axiom
comparison is still required after compilation.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess


def body(source):
    source = source.replace('\r\n', '\n').lstrip('\ufeff')
    lines = []
    for line in source.splitlines():
        if re.fullmatch(r'\s*module\s*', line):
            continue
        if re.match(r'^(?:public\s+)?import(?:\s+all)?\s', line):
            continue
        if line.strip() in {'@[expose] public section', 'public section',
                            'set_option backward.privateInPublic true',
                            'set_option backward.proofsInPublic true'}:
            continue
        if line.strip():
            lines.append(line.rstrip())
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('baseline')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', args.baseline],
                                    cwd=root, text=True).splitlines()
    rows = []
    for name in paths:
        if not name.endswith('.lean') or name == 'lakefile.lean':
            continue
        before = subprocess.check_output(['git', 'show', f'{args.baseline}:{name}'], cwd=root)
        path = root / name
        after = path.read_bytes()
        old = before.decode('utf-8-sig')
        new = after.decode('utf-8-sig')
        if body(old) != body(new):
            raise RuntimeError(f'Mathematical source changed: {name}')
        if not re.search(r'^module\s*$', new, re.M):
            raise RuntimeError(f'Missing module header: {name}')
        rows.append({'path': name, 'before_sha256': hashlib.sha256(before).hexdigest(),
                     'after_sha256': hashlib.sha256(after).hexdigest(),
                     'normalized_body_sha256': hashlib.sha256(body(new).encode()).hexdigest()})
    report = {'status': 'PASS', 'scope': 'unchanged normalized mathematical source; not compiler certification',
              'baseline': args.baseline, 'files': rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(f'PASS: {len(rows)} source files preserve their mathematical bodies.')


if __name__ == '__main__':
    main()
