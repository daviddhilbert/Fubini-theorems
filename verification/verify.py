#!/usr/bin/env python3
"""Check source ownership and every preserved public Fubini signature/axiom list."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys

from lean_source import code_only, declarations

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((ROOT / 'SOURCE-MANIFEST.json').read_text())
    contract = json.loads((HERE / 'public-contract.json').read_text())['declarations']
    owned = json.loads((HERE / 'owned-declarations.json').read_text())
    pins = json.loads((ROOT / 'lake-manifest.json').read_text())
    by_name = {p['name'].strip('«»'): p for p in pins['packages']}
    expected = {
        'hilbert-mathlib': manifest['providers']['shared_provider_commit'],
        'acvf_qe': manifest['providers']['qe_shared_commit'],
        'special_transformations': manifest['providers']['fubini_special_provider'],
        'integration_in_acvf': manifest['providers']['fubini_integration_provider'],
        'mathlib': '56a005855ea17e0b0958f73ec801ae140b0a1679',
    }
    provider_state = {}
    for name, revision in expected.items():
        package = ROOT / pins['packagesDir'] / name
        check(by_name[name]['rev'] == revision, 'Unexpected provider pin: ' + name)
        actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=package, text=True).strip()
        check(actual == revision, 'Unexpected provider checkout: ' + name)
        dirty = subprocess.check_output(['git', 'diff', 'HEAD', '--name-only', '--', '*.lean'], cwd=package, text=True)
        check(not dirty, 'Changed provider Lean sources: ' + name)
        provider_state[name] = revision
    check((ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0',
          'Unexpected Lean toolchain')
    sources = {}
    names = []
    for item in manifest['modules']:
        path = ROOT / item['target_path']
        check(digest(path) == item.get('module_sha256', item['extracted_sha256']), 'Source fingerprint mismatch: ' + str(path))
        sources[item['target_path']] = digest(path)
        content = path.read_text()
        masked = code_only(content)
        check(not re.search(r'\b(?:sorry|admit|axiom)\b', masked), 'Unproved source declaration: ' + str(path))
        check(not re.search(r'^(?:(?:public|private)\s+)?import\s+(?:DiamondIntegral\b|«section )',
                            masked, re.M), 'Diamond dependency in independent Fubini source: ' + str(path))
        names.extend(d['name'] for d in declarations(content))
    check(names == [d['name'] for d in owned], 'Owned declaration inventory changed')
    check(len(names) == len(set(names)), 'Duplicate implementation owner')
    check(set(d['name'] for d in contract) == set(names) | set(manifest['inherited_declarations']),
          'Original public contract is not covered by owned and inherited declarations')
    entry_points = {}
    for relative, expected_hash in manifest['entry_points'].items():
        path = ROOT / relative
        check(digest(path) == expected_hash, 'Changed subject entry point: ' + relative)
        masked = code_only(path.read_text())
        check(not re.search(r'\b(?:sorry|admit|axiom)\b', masked), 'Unproved entry point: ' + relative)
        check(not declarations(path.read_text()), 'Subject entry point introduces declarations: ' + relative)
        entry_points[relative] = digest(path)
    actual_sources = {str(path.relative_to(ROOT)) for path in (ROOT / 'FubiniTheorems').rglob('*.lean')}
    actual_sources.add('FubiniTheorems.lean')
    check(actual_sources == set(sources) | set(entry_points), 'Uninventoried or missing Fubini source')
    # Reuse the already checked parser at the exact shared-library revision.
    parser_path = ROOT / pins['packagesDir'] / 'hilbert-mathlib/verification/verify.py'
    spec = importlib.util.spec_from_file_location('shared_signature_parser', parser_path)
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    scratch = ROOT / '.scratch'
    scratch.mkdir(exist_ok=True)
    commands = ['import FubiniTheorems', 'set_option pp.universes true',
                'set_option pp.fullNames true', 'set_option pp.notation false',
                'set_option format.width 160']
    for item in contract:
        commands += ['#check @' + item['name'], '#print axioms ' + item['name']]
    audit = scratch / 'PublicSignatures.lean'
    audit.write_text('\n'.join(commands) + '\n')
    result = subprocess.run(['lake', 'env', 'lean', str(audit)], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (scratch / 'public-signatures.txt').write_text(result.stdout)
    check(result.returncode == 0, 'Public type audit failed; see .scratch/public-signatures.txt')
    actual = parser.records(result.stdout)
    check(len(actual) == len(contract), 'Missing signature or axiom records')
    for before, after in zip(contract, actual):
        check(before['name'] == after['name'], 'Public declaration order changed')
        signature = hashlib.sha256(after['signature'].encode()).hexdigest()
        check(signature == before['signature_sha256'], 'Changed public type: ' + before['name'])
        check(before['axioms'] == after['axioms'], 'Changed axiom inventory: ' + before['name'])
    check(sources == {p: digest(ROOT / p) for p in sources}, 'Source changed during the audit')
    check(entry_points == {p: digest(ROOT / p) for p in entry_points}, 'Entry point changed during the audit')
    receipt = {'status': 'PASS', 'modules': len(sources), 'owned_declarations': len(names),
               'preserved_public_types': len(contract),
               'inherited_declarations': manifest['inherited_declarations'],
               'providers': provider_state, 'source_sha256': sources,
               'entry_point_sha256': entry_points,
               'full_type_output_sha256': hashlib.sha256(result.stdout.encode()).hexdigest(),
               'principles': ['propext', 'Classical.choice', 'Quot.sound']}
    (scratch / 'verification-status.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('PASS:', len(sources), 'source modules;', len(contract), 'unchanged full public types and axiom inventories.')


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError, ValueError) as error:
        print('FAIL:', error, file=sys.stderr)
        sys.exit(1)
