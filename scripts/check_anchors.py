#!/usr/bin/env python3
"""Check, or refresh, every Lean source anchor of the paper and the blueprint.

An anchor names a declaration, a library file and a line. It is valid when the
declaration index of `scripts/lean_anchors.py` assigns exactly that file and
line to the fully qualified name, the line declares that name, and the name is
in the public contract. The proof map also fingerprints each anchored file.

Registries checked:
  paper/PROOF-MAP.json                  steps[].declarations[]
  blueprint/nodes.json                  [].declarations[]
  blueprint/src/source-links.tsv        name -> file#Lline, equal to nodes.json
  blueprint/proof-source-manifest.json  proof inputs and the linked revision

With --write, lines, files and fingerprints are recomputed from the index and
the four registries are rewritten; names are never changed.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lean_anchors  # noqa: E402

ROOT = lean_anchors.ROOT
PROOF_MAP = ROOT / 'paper/PROOF-MAP.json'
NODES = ROOT / 'blueprint/nodes.json'
LINKS = ROOT / 'blueprint/src/source-links.tsv'
RECEIPT = ROOT / 'blueprint/proof-source-manifest.json'
PROOF_INPUTS = ['SOURCE-MANIFEST.json', 'lake-manifest.json', 'lakefile.toml', 'lean-toolchain',
                'verification/public-contract.json']


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def library_files():
    files = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / 'FubiniTheorems').rglob('*.lean'))
    return files + ['FubiniTheorems.lean']


def dump(path, data):
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--write', action='store_true', help='refresh anchors and fingerprints in place')
    args = parser.parse_args()
    index = lean_anchors.index()
    contract = {d['name'] for d in json.loads((ROOT / 'verification/public-contract.json').read_text())['declarations']}
    errors = []

    def anchor(declaration, where, fingerprint):
        name = declaration['name']
        if name not in index:
            errors.append(f'{where}: no declaration {name} in the library')
            return
        file, line = index[name]
        if args.write:
            declaration['file'], declaration['line'] = file, line
            if fingerprint:
                declaration['source_sha256'] = digest(ROOT / file)
        if (declaration['file'], declaration['line']) != (file, line):
            errors.append(f'{where}: {name} is declared at {file}:{line}, '
                          f'not {declaration["file"]}:{declaration["line"]}')
        elif not lean_anchors.line_matches(ROOT, file, line, name):
            errors.append(f'{where}: line {file}:{line} does not declare {name}')
        if fingerprint and declaration.get('source_sha256') != digest(ROOT / file):
            errors.append(f'{where}: stale fingerprint for {file}')
        if name not in contract:
            errors.append(f'{where}: {name} is outside the public contract')

    proof_map = json.loads(PROOF_MAP.read_text(encoding='utf-8'))
    paper_anchors = 0
    for number, step in enumerate(proof_map['steps'], 1):
        if not (ROOT / step['section']).is_file():
            errors.append(f'PROOF-MAP step {number}: missing section {step["section"]}')
        for declaration in step['declarations']:
            anchor(declaration, f'PROOF-MAP step {number} ({step["step"]})', True)
            paper_anchors += 1

    nodes = json.loads(NODES.read_text(encoding='utf-8'))
    registry = {}
    for node in nodes:
        for declaration in node['declarations']:
            anchor(declaration, f'blueprint node {node["id"]}', False)
            registry[declaration['name']] = f'{declaration["file"]}#L{declaration["line"]}'

    receipt = json.loads(RECEIPT.read_text(encoding='utf-8'))
    inputs = library_files() + PROOF_INPUTS
    if args.write:
        dump(PROOF_MAP, proof_map)
        dump(NODES, nodes)
        LINKS.write_text(''.join(f'{name}\t{target}\n' for name, target in registry.items()), encoding='utf-8')
        receipt['sha256'] = {name: digest(ROOT / name) for name in inputs}
        dump(RECEIPT, receipt)

    links = dict(line.split('\t') for line in LINKS.read_text(encoding='utf-8').splitlines())
    if links != registry:
        errors.append('source-links.tsv differs from the declarations of nodes.json')
    if set(receipt['sha256']) != set(inputs):
        errors.append('proof-source-manifest.json does not list exactly the library sources and proof inputs')
    for name, expected in receipt['sha256'].items():
        if (ROOT / name).is_file() and digest(ROOT / name) != expected:
            errors.append(f'proof input changed: {name}')

    revision = receipt['proof_revision']
    available = subprocess.run(['git', 'cat-file', '-e', revision + '^{commit}'], cwd=ROOT,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
    if available:
        same = subprocess.run(['git', 'diff', '--quiet', revision, '--', 'FubiniTheorems', 'FubiniTheorems.lean'],
                              cwd=ROOT).returncode == 0
        if not same:
            errors.append(f'Lean sources differ from the linked revision {revision}')
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        sys.exit(1)
    print(json.dumps({'status': 'PASS', 'paper_anchors': paper_anchors,
                      'blueprint_declarations': len(registry), 'proof_inputs': len(inputs),
                      'linked_revision': revision,
                      'linked_revision_tree': 'identical' if available else 'not available locally'}))


if __name__ == '__main__':
    main()
