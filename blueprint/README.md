# Fubini theorems blueprint

This blueprint follows Forey–Yin, *Bounded integral and motivic Milnor fiber*,
[arXiv:1910.12764v2](https://arxiv.org/abs/1910.12764v2), Section 5. It has
33 selected mathematical nodes and links 50 Lean declarations: bounded Fubini
([Theorem 5.17](https://arxiv.org/html/1910.12764v2#Thmtheorem5.17)) from the
original ground and fibre hypothesis to the discharged theorem, the bounded
and geometric Fubini theorems for fibre representatives of mixed degree, the
inflated-family Fubini theorem, the saturated Puiseux ambient and the
inflated-family motivic volume. This is a selected mathematical dependency
graph, not the complete expression-level graph of the library.

The source links are pinned to `5b547c1ab198c59ca380993afb3a779579696a80`,
whose Lean sources are byte-identical to those of this release. The library
build (13,134 jobs) and all 11,195 public type/axiom checks of
[the public contract](https://github.com/daviddhilbert/Fubini-theorems/blob/5b547c1ab198c59ca380993afb3a779579696a80/verification/public-contract.json)
passed. `proof-source-manifest.json` fingerprints the proof sources, pins and
contract used here. Documentation validation is separate from Lean compilation.

## Build and preview

With Python, Graphviz and its development headers available, run at repo root:

```sh
python -m pip install -r blueprint/requirements.txt
python scripts/check_anchors.py
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
`src/source-links.tsv` fixes the corresponding source links. Keep them in sync:
after a change of the Lean sources, `python scripts/check_anchors.py --write`
recomputes the anchor lines and fingerprints of the blueprint and of the
paper's proof map, and `python scripts/check_anchors.py` checks every anchor
against the declaration index of the library. Green nodes refer to the
compiled source snapshot recorded by that receipt.

## Reuse and attribution

The blueprint scaffolding, clickable graph helper and validation script are
adapted from the MIT-licensed
[ACVF-QE blueprint](https://github.com/daviddhilbert/ACVF-QE/tree/939346b0a99899e22a873479364e3cc5d142731c/blueprint),
which in turn credits the Special transformations blueprint. The renderer is
Patrick Massot's `leanblueprint` 0.0.20. Mathematical source authors are Arthur
Forey and Yimu Yin. Existing proof-source notices and provider licenses remain
in place.
