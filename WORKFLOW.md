# Proof and extraction workflow

Use the pinned toolchain and exact dependency manifest. Preserve unrelated
author work and the public declaration names, mathematical hypotheses,
parameter scope and conventions of the checked development.

This package depends only on its recorded lower-level providers; it must not
depend on diamond-integral. Shared paper-independent definitions belong in
hilbert-mathlib. The common LRV encoding belongs in ACVF-QE. Keep the package
graph acyclic and search the existing providers before rebuilding a result.

Preserve exact source revisions, original notices and applicable licenses.
During an extraction, change implementation ownership and imports separately
from any mathematical generalization. Validate the new provider and unchanged
full theorem types before replacing a consumer proof body with an import.

Run `lake build FubiniTheorems` and `python3 verification/verify.py`.
Verification requires source compilation, full public types and axiom reports
allowing only propext, Classical.choice and Quot.sound. Inspect explicit
hypotheses: a clean axiom list does not discharge an assumed mathematical
input. Do not introduce proof placeholders, custom axioms or synthetic
structures that assume the desired result.

Keep scratch sources and compiler output in .scratch/. Do not edit sources
during their compiler certification. Update the source manifest and public
contract deliberately when an authorized mathematical statement changes.
Check affected downstream imports and exact provider pins before retiring
compatibility paths. Publish only within the author's authorization and
report actual source, type, axiom and CI outcomes.

For a future Palomar submission, select a couple of main mathematical results
and state their exact hypotheses. Whole-paper coverage and registration of
every section are not required unless the author explicitly requests them.
Consult Palomar's current guidelines and complete its checks for that selection.
This standing author rule also applies to future formalization projects.

The current author selection is narrower: **only Theorem 5.17**, stated as
`FubiniStatement.bounded_fubini`, is the advertised Challenge result. Necessary
definition helpers may accompany its independent vocabulary; supporting research
results remain in the library and blueprint. The author permits a concise
standalone statement rather than an exact copy of the older exported type.
Preserve the existing library declarations. The Solution constructs the intrinsic
RES presentation and proves its Fubini statement from
`DiamondIntegral.Section5.bounded_fubini_discharged`. See
`palomar/definition-helpers.json` for the construction specifications.

For blueprint edits, run `python3 scripts/check_blueprint.py`,
`leanblueprint web`, and `python3 scripts/check_blueprint.py --rendered`.
Run `python3 scripts/check_palomar.py --output palomar/readiness.json` for local
source, selection and size checks. Run `lake build Challenge Solution` and
Comparator with independent NanoDa replay, then the pinned full workflow on
the immutable public snapshot. Ordinary library compilation is separate evidence.
