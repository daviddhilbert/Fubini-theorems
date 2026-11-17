# Bounded Fubini blueprint

This blueprint follows Forey–Yin, *Bounded integral and motivic Milnor fiber*,
[arXiv:1910.12764v2, Theorem 5.17](https://arxiv.org/html/1910.12764v2#Thmtheorem5.17).
It has 18 selected mathematical nodes and links 22 Lean declarations, from the
original ground and fibre hypothesis to the discharged bounded Fubini theorem.
Supporting nodes explain the proof; only the final theorem is selected for
Palomar. This is a selected mathematical dependency graph, not the complete
expression-level graph of the 1,795-file library.

The source links are pinned to `58506df2ed62eafc66d3cb00be8ee24c57597449`, whose
[source build and 10,566 public type/axiom checks passed](https://github.com/daviddhilbert/Fubini-theorems/blob/58506df2ed62eafc66d3cb00be8ee24c57597449/palomar/module-verification.json).
`proof-source-manifest.json` fingerprints the proof sources, pins and contract
used here. Documentation validation is separate from Lean compilation and
Palomar's Comparator/NanoDa checks.

## Build and preview

With Python, Graphviz and its development headers available, run at repo root:

```sh
python -m pip install -r blueprint/requirements.txt
python scripts/check_blueprint.py
leanblueprint web
python scripts/check_blueprint.py --rendered
```

Open `blueprint/web/index.html` and select **Open the theorem dependency graph**.
The standalone SVG links to each statement and works from a local file.
`leanblueprint serve` provides the interactive sidebar. The optional print
source is `src/print.tex`; `leanblueprint pdf` requires LaTeX and `latexmk`.

`src/content.tex` contains the mathematical statements and proof outlines.
`nodes.json` records the selected graph and declaration anchors;
`src/source-links.tsv` fixes the corresponding source links. Keep them in sync.
Green nodes refer to the compiled source snapshot recorded by that receipt.

## Reuse and attribution

The blueprint scaffolding, clickable graph helper and validation script are
adapted from the MIT-licensed
[ACVF-QE blueprint](https://github.com/daviddhilbert/ACVF-QE/tree/939346b0a99899e22a873479364e3cc5d142731c/blueprint),
which in turn credits the Special transformations blueprint. The renderer is
Patrick Massot's `leanblueprint` 0.0.20. Mathematical source authors are Arthur
Forey and Yimu Yin. Existing proof-source notices and provider licenses remain
in place. See [the preparation record](../PALOMAR-PREPARATION.md) for submission
scope and outstanding checks.
