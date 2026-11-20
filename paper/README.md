# Fubini theorems for motivic volume

The manuscript follows the notation and AMS article format of the diamond-integral
paper. It gives the monomial decomposition, bounded and geometric Fubini proofs,
their versions for fibre representatives of mixed degree, the inflated-family
Fubini theorem, the finite Kummer comparison with the inflated-family volume,
and the variety vanishing corollary. The mathematical text contains no
formalization or editorial-history discussion.

Source: `fubini-theorems.tex` and `sections/`.
Compiled PDF: `../output/pdf/fubini-theorems.pdf`.

Build from the repository root with a LaTeX distribution:

```sh
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../output/pdf paper/fubini-theorems.tex
```

Alternatively:

```sh
tectonic --outdir output/pdf --keep-logs paper/fubini-theorems.tex
```

`SOURCES.json` records the fingerprints of the approved mathematical source
fragments used in preparing the manuscript. It is separate from the paper.

`PROOF-MAP.json` records the correspondence between the manuscript's proof
steps and the Lean declarations, including source hashes and line anchors.
The proof routes use Smith bases, cylindrical Euler certificates, complete
witness graphs fixed before preparation, common-degree geometric padding,
thickening of vanishing labels, relative monomial charts and a base partition
obtained by Gamma fibre integration.
Run `python3 scripts/check_paper.py` from the repository root to check that
the reviewed text and source anchors have not changed, and
`python3 scripts/check_anchors.py` to check every anchor against the
declaration index of the library. After the full Lean
audit, `--verified-types` also checks its current-source receipt. This identity
check supplements the manual mathematical review; it does not verify prose.
