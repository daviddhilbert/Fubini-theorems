#!/usr/bin/env python3
"""Index the declaration lines of the Fubini library sources.

The index tracks `namespace`, `section` and `end` commands and skips block
comments, so each entry records the fully qualified name of a declaration and
the 1-based line on which its keyword occurs. It is used to re-anchor and to
check the source links of the paper's proof map and of the blueprint.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)*'
    r'(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*'
    r'(theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+'
    r'(?!:)([^\s:({\[]+)')
NAMESPACE = re.compile(r'^namespace\s+(\S+)')
SECTION = re.compile(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$')
END = re.compile(r'^end(?:\s+(\S+))?\s*$')


def strip_comments(lines):
    """Yield (line_number, text) with block and line comments removed."""
    depth = 0
    for number, line in enumerate(lines, 1):
        out = []
        i = 0
        while i < len(line):
            if line.startswith('/-', i):
                depth += 1
                i += 2
            elif depth and line.startswith('-/', i):
                depth -= 1
                i += 2
            elif not depth and line.startswith('--', i):
                break
            else:
                if not depth:
                    out.append(line[i])
                i += 1
        yield number, ''.join(out)


def declarations(path):
    """Return {full_name: line} for one Lean source file."""
    stack = []  # entries: ('ns', [components]) or ('sec', name)
    found = {}
    lines = path.read_text(encoding='utf-8-sig').splitlines()
    for number, text in strip_comments(lines):
        text = text.strip()
        if not text:
            continue
        m = NAMESPACE.match(text)
        if m:
            stack.append(('ns', m[1].split('.')))
            continue
        m = SECTION.match(text)
        if m:
            stack.append(('sec', m[1]))
            continue
        m = END.match(text)
        if m:
            if stack:
                stack.pop()
            continue
        m = DECL.match(text)
        if m and m[1] != 'instance':
            name = m[2]
            if name.startswith('_root_.'):
                full = name[len('_root_.'):]
            else:
                prefix = [c for kind, value in stack if kind == 'ns' for c in value]
                full = '.'.join(prefix + [name])
            found.setdefault(full, number)
    return found


def index(root=ROOT):
    """Return {full_name: (relative_file, line)} for the whole library."""
    result = {}
    files = sorted((root / 'FubiniTheorems').rglob('*.lean')) + [root / 'FubiniTheorems.lean']
    for path in files:
        rel = path.relative_to(root).as_posix()
        for name, line in declarations(path).items():
            result.setdefault(name, (rel, line))
    return result


def line_matches(root, file, line, name):
    """Check that `line` of `file` declares the last component of `name`."""
    text = (root / file).read_text(encoding='utf-8-sig').splitlines()[line - 1]
    short = re.escape(name.rsplit('.', 1)[-1])
    return re.match(
        r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*'
        r'(?:theorem|lemma|def|abbrev|structure|class|inductive)\s+(?:[\w.]+\.)?'
        + short + r'(?![\w.\'])', text) is not None
