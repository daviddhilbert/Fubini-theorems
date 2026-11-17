#!/usr/bin/env python3
"""Fail-closed local preparation checks; not Palomar's official verifier."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'verification'))
from lean_source import code_only, declarations

MAIN = 'FubiniStatement.bounded_fubini'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    blockers = []
    config = json.loads((ROOT / 'comparator.json').read_text())
    inventory_path = ROOT / 'palomar/definition-helpers.json'
    inventory = json.loads(inventory_path.read_text()) if inventory_path.exists() else {}
    helper_theorems = [item['name'] for item in inventory.get('theorem_helpers', [])]
    helper_definitions = [item['name'] for item in inventory.get('definition_helpers', [])]
    if not inventory:
        blockers.append('Necessary definition-helper inventory has not been recorded.')
    if config.get('challenge_module') != 'Challenge' or config.get('solution_module') != 'Solution':
        blockers.append('Unexpected Challenge/Solution module selection.')
    if config.get('theorem_names') != [MAIN] + helper_theorems:
        blockers.append('Selection must contain only bounded Fubini and its inventoried definition helpers.')
    if config.get('definition_names', []) != helper_definitions:
        blockers.append('Definition holes differ from their specification inventory.')
    if config.get('permitted_axioms') != ['propext', 'Classical.choice', 'Quot.sound']:
        blockers.append('Only the standard three axioms are allowed.')
    challenge = ROOT / 'Challenge.lean'
    source = challenge.read_text()
    code = code_only(source)
    theorems = [d['name'] for d in declarations(source) if d['kind'] in ('theorem', 'lemma')]
    if set(theorems) != set([MAIN] + helper_theorems) or len(theorems) != len(set(theorems)):
        blockers.append('Challenge theorem declarations differ from the one headline and necessary definition helpers.')
    imports = re.findall(r'^\s*(?:public\s+)?import\s+(\S+)', code, re.M)
    # Deliberately conservative: the draft must first reach the Mathlib-only
    # shape. Official preflight must authenticate the entire import closure.
    forbidden = [m for m in imports if not any(m == p or m.startswith(p + '.') for p in ('Mathlib', 'Init', 'Lean', 'Std'))]
    if forbidden:
        blockers.append('Challenge imports project-specific sources; independent vocabulary is required.')
    lines = len(source.splitlines())
    size = len(challenge.read_bytes())
    if lines > 1000 or size > 100 * 1024:
        blockers.append('Challenge exceeds the hard 1,000-line / 100-KiB limit.')
    # The author selects a concise standalone presentation. The original
    # public theorem remains untouched; the Solution constructs the vocabulary
    # and proves the new presentation via the original bounded Fubini theorem.
    # Comparator, rather than a source-string comparison, judges the new type.
    proof = ROOT / 'FubiniStatement/BoundedFubini.lean'
    if not proof.exists() or 'bounded_fubini_discharged' not in code_only(proof.read_text()):
        blockers.append('Missing proof bridge to the existing bounded Fubini theorem.')
    missing_module = []
    oversized = []
    unproved = []
    symlinks = []
    files = []
    for path in sorted(ROOT.rglob('*.lean')):
        rel = path.relative_to(ROOT)
        if {'.git', '.lake', '.scratch'}.intersection(rel.parts):
            continue
        # This check describes the intended tracked tree; .scratch is not
        # committed. Palomar scans every committed Lean source, including archives.
        files.append(str(rel))
        if path.is_symlink():
            symlinks.append(str(rel))
            continue
        text = path.read_text(encoding='utf-8-sig')
        masked = code_only(text)
        if path.name != 'lakefile.lean' and not re.match(r'^\s*module\b', masked):
            missing_module.append(str(rel))
        if len(text.splitlines()) > 10000:
            oversized.append(str(rel))
        if path != challenge and re.search(r'\b(?:sorry|admit|axiom)\b', masked):
            unproved.append(str(rel))
    for paths, message in [
        (missing_module, 'Lean sources still require module-format migration'),
        (oversized, 'Lean sources exceed 10,000 physical lines'),
        (symlinks, 'Lean source symlinks are not allowed'),
        (unproved, 'Proof sources contain unproved declarations'),
    ]:
        if paths:
            blockers.append(f'{message}: {len(paths)} files.')
    for name in ['formalization.yaml', 'LICENSE', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'Solution.lean']:
        if not (ROOT / name).is_file():
            blockers.append(f'Missing required file: {name}')
    report = {
        'status': 'BLOCKED' if blockers else 'LOCAL_CHECKS_PASS',
        'scope': 'preparation checks only; not official Palomar verification',
        'advertised_theorems': [MAIN], 'definition_helper_theorems': helper_theorems,
        'theorem_names': theorems,
        'challenge': {'lines': lines, 'bytes': size, 'imports': imports,
                      'project_imports': forbidden, 'sha256': hashlib.sha256(challenge.read_bytes()).hexdigest()},
        'lean_source_files': len(files), 'missing_module': missing_module,
        'oversized': oversized, 'symlinks': symlinks, 'unproved_proof_sources': unproved,
        'blockers': blockers,
        'required_external_checks': ['Exact-snapshot Comparator', 'Independent NanoDa replay',
                                     'Official Palomar preflight'],
        'external_check_status': 'Not verified by this script; see palomar/verification.json',
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k not in {'missing_module', 'oversized', 'symlinks', 'unproved_proof_sources'}}, indent=2))
    return int(bool(blockers))


if __name__ == '__main__':
    sys.exit(main())
