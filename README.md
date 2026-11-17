# Fubini theorems

[![Lean verification](https://github.com/daviddhilbert/Fubini-theorems/actions/workflows/lean.yml/badge.svg)](https://github.com/daviddhilbert/Fubini-theorems/actions/workflows/lean.yml)

Lean formalization of the active results of Section 5 of Forey and Yin's
*Bounded integral and motivic Milnor fiber*, including the monomial decomposition,
canonical Puiseux-model comparison, bounded and geometric Fubini theorems,
and the variety corollary, with all of their local prerequisites.

The [Lean blueprint](blueprint/README.md) follows the main bounded Fubini proof
through its exact model, ground and fibre hypotheses. After rendering, open
`blueprint/web/index.html` for the statements and clickable dependency graph.
The [Palomar preparation record](PALOMAR-PREPARATION.md) selects **Theorem 5.17
only**, stated as `FubiniStatement.bounded_fubini`. Its independent Challenge
uses an intrinsic reduced RES ring and the necessary
[definition certificates](palomar/definition-helpers.json). The Solution proves
this presentation from the existing bounded Fubini theorem. The full library
build and all 10,566 unchanged public type/axiom comparisons have passed.

The [traditional mathematical paper](paper/fubini-theorems.tex) is available
as a [compiled PDF](output/pdf/fubini-theorems.pdf). Its proof steps follow
the checked Lean routes; [the separate proof map](paper/PROOF-MAP.json) records
19 steps and 43 declaration anchors.

The proof implementation is independent of the diamond-integral package.
It uses exact revisions of hilbert-mathlib, ACVF-QE, special-transformations,
and integration-in-ACVF. Original public declaration namespaces are retained
for compatibility. Mathematical hypotheses and theorem statements are those
of the checked source development.

## Organization

- `Prerequisites/Definability`: the required definability background.
- `Prerequisites/Grothendieck`: coefficient presentations and tensor prerequisites.
- `Prerequisites/Euler`: the required Euler and comparison constructions.
- `Decomposition`: the monomial and value-group arguments.
- `Comparison`: coefficient comparisons and concrete Puiseux models.
- `Fubini`: lifting interfaces and bounded/geometric integration results.
- `Corollaries`: the concluding variety results.

`FubiniTheorems.Library` preserves the complete original Section 5 entry point.
Subject entry points are also available. The source inventory and exact
implementation owners are recorded in `SOURCE-MANIFEST.json`.

## Main results

The declaration names below have the prefix `DiamondIntegral.Section5.`.
Original names are retained so existing mathematical clients keep compiling.

| Result | Declaration | Source |
| --- | --- | --- |
| Lemma 5.12: monomial decomposition | `monomial_decomposition_5_12` | [MonomialMatrixForm](FubiniTheorems/Decomposition/MonomialMatrixForm.lean) |
| Remark 5.13: concrete Galois identifications | `PuiseuxOriginal.remark_5_13` | [PuiseuxInducedRV](FubiniTheorems/Comparison/PuiseuxModels/PuiseuxInducedRV.lean) |
| Comparison 5.14 | `PuiseuxOriginal.theta_5_14_concrete` | [PuiseuxConcreteComparisons](FubiniTheorems/Comparison/PuiseuxModels/PuiseuxConcreteComparisons.lean) |
| Theorem 5.17: bounded Fubini | `bounded_fubini_discharged` | [Section5DischargedInputs](FubiniTheorems/Fubini/Section5DischargedInputs.lean) |
| Geometric Fubini | `geometric_fubini_discharged` | [Section5DischargedInputs](FubiniTheorems/Fubini/Section5DischargedInputs.lean) |
| Variety corollary | `PuiseuxOriginal.corollary_global_vanishing_discharged` | [VarietyCorollaryDischarged](FubiniTheorems/Corollaries/VarietyCorollaryDischarged.lean) |

The source statements retain their actual model, base and parameter hypotheses.
The public contract verifier checks their full types together with all
inventoried prerequisites.

## Build and verify

```sh
lake exe cache get
lake build FubiniTheorems Challenge Solution
python3 verification/verify.py
```

Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 are pinned.
CI compiles the library, checks all source fingerprints, and compares the
10,566 inventoried public types and axiom inventories with their checked
pre-extraction baseline. The finite-laws prerequisite is owned by
special-transformations and remains part of that public contract.
Only `propext`, `Classical.choice`, and `Quot.sound` are accepted.
Full current type/axiom output is retained as a CI artifact.

The first independent source build and complete public contract audit passed
in [GitHub Actions](https://github.com/daviddhilbert/Fubini-theorems/actions/runs/43987163120)
at [the extracted mathematical revision](https://github.com/daviddhilbert/Fubini-theorems/commit/fea1092a0a3e0b6bcde5453c3083151f16d747f9).
`EXTRACTION-STATUS.json` records that checkpoint; the badge shows current CI.

The two former scoped [18] source patches are retired. The unmeasured
lifting/kernel input uses the published generated-base proof through a
proved presentation bridge. The extraction adds no mathematical assumptions.
The abandoned cross-section computation material is outside this scope.
The independent [source-boundary check](verification/independence-boundary.json)
records that Section 5's original full closure uses no modules or constants
from this paper's Section 6, whose Gamma-kernel repairs are separate work.

## Provenance and workflow

See `WORKFLOW.md` and `AGENTS.md`. Source comments and original notices are
retained; dependencies retain their own licenses. In particular, the
Newton–Puiseux and Grothendieck-ring adaptations remain in hilbert-mathlib
with their Apache 2.0 notices and license texts.
