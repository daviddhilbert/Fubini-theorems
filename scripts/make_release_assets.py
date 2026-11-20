#!/usr/bin/env python3
"""Assemble the release assets of a Fubini theorems version.

Reproduces the v0.1.0 asset set: the compiled paper, the paper source
archive, the rendered blueprint archive, the compressed public type and
axiom output, a verification record and SHA256SUMS. Archives are written
deterministically, without owner names or timestamps.

Run from a clean checkout of the release commit after
  lake build FubiniTheorems; python3 verification/verify.py
  python3 scripts/check_anchors.py; python3 scripts/check_blueprint.py
  python3 scripts/check_paper.py --verified-types
and, for the blueprint archive, after `leanblueprint web` and
`python3 scripts/check_blueprint.py --rendered` (or after unpacking the
`fubini-blueprint` artifact of the blueprint workflow into blueprint/web).
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import io
import json
import subprocess
import tarfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
EPOCH = (2026, 11, 19, 0, 0, 0)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(*command):
    return subprocess.run(command, cwd=ROOT, text=True, capture_output=True)


def check_output(*command):
    result = run(*command)
    if result.returncode:
        raise SystemExit(f'{" ".join(command)} failed:\n{result.stdout}{result.stderr}')
    return json.loads(result.stdout.strip().splitlines()[-1])


def tar_directory(source, prefix, target):
    with gzip.GzipFile(target, 'wb', mtime=0) as stream:
        with tarfile.open(fileobj=stream, mode='w', format=tarfile.USTAR_FORMAT) as archive:
            for path in sorted(p for p in source.rglob('*') if p.is_file()):
                data = path.read_bytes()
                info = tarfile.TarInfo(f'{prefix}/{path.relative_to(source).as_posix()}')
                info.size, info.mode, info.mtime = len(data), 0o644, 0
                archive.addfile(info, io.BytesIO(data))


def zip_directory(source, target):
    with zipfile.ZipFile(target, 'w', zipfile.ZIP_DEFLATED) as archive:
        for path in sorted(p for p in source.rglob('*') if p.is_file()):
            info = zipfile.ZipInfo(path.relative_to(source).as_posix(), EPOCH)
            info.compress_type, info.external_attr = zipfile.ZIP_DEFLATED, 0o644 << 16
            archive.writestr(info, path.read_bytes())


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('version', help='for example 0.2.0')
    parser.add_argument('out', type=Path, help='output directory, outside the repository')
    parser.add_argument('--build-jobs', type=int, required=True,
                        help='job count reported by `lake build FubiniTheorems`')
    args = parser.parse_args()
    version, out = args.version, args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if run('git', 'diff', '--quiet', 'HEAD').returncode:
        raise SystemExit('The checkout has uncommitted changes.')
    revision = run('git', 'rev-parse', 'HEAD').stdout.strip()

    anchors = check_output('python3', 'scripts/check_anchors.py')
    paper = check_output('python3', 'scripts/check_paper.py', '--verified-types')
    web = ROOT / 'blueprint/web'
    rendered = (web / 'index.html').is_file()
    blueprint = check_output('python3', 'scripts/check_blueprint.py', *(['--rendered'] if rendered else []))
    status = json.loads((ROOT / '.scratch/verification-status.json').read_text())

    assets = [ROOT / 'output/pdf/fubini-theorems.pdf']
    (out / 'fubini-theorems.pdf').write_bytes(assets[0].read_bytes())
    tar_directory(ROOT / 'paper', 'paper', out / f'fubini-paper-source-v{version}.tar.gz')
    if rendered:
        zip_directory(web, out / f'fubini-blueprint-v{version}.zip')
    else:
        (out / f'fubini-blueprint-v{version}.zip').unlink(missing_ok=True)
    with gzip.GzipFile(out / f'public-types-and-axioms-v{version}.txt.gz', 'wb', mtime=0) as stream:
        stream.write((ROOT / '.scratch/public-signatures.txt').read_bytes())
    receipt = json.loads((ROOT / 'blueprint/proof-source-manifest.json').read_text())
    record = {
        'release_revision': revision,
        'source_revision': receipt['proof_revision'],
        'library_build': {'command': 'lake build FubiniTheorems', 'status': 'PASS', 'jobs': args.build_jobs},
        'library_verification': {'command': 'python3 verification/verify.py', **status},
        'paper_build': json.loads((ROOT / 'paper/BUILD.json').read_text()),
        'paper_checks': {'command': 'python3 scripts/check_paper.py --verified-types', **paper},
        'anchor_checks': {'command': 'python3 scripts/check_anchors.py', **anchors},
        'blueprint': {'command': 'python3 scripts/check_blueprint.py' + (' --rendered' if rendered else ''),
                      **blueprint},
    }
    (out / f'verification-v{version}.json').write_text(json.dumps(record, indent=2) + '\n')
    names = ['fubini-theorems.pdf', f'fubini-blueprint-v{version}.zip', f'fubini-paper-source-v{version}.tar.gz',
             f'public-types-and-axioms-v{version}.txt.gz', f'verification-v{version}.json']
    present = [name for name in names if (out / name).is_file()]
    (out / 'SHA256SUMS').write_text(''.join(f'{digest(out / name)}  {name}\n' for name in present))
    print(json.dumps({'release_revision': revision, 'assets': present,
                      'blueprint_archive': 'written' if rendered else 'missing: render blueprint/web first'}))


if __name__ == '__main__':
    main()
