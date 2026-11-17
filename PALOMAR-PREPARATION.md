# Bounded Fubini — preparation record

The only advertised research result is **Forey–Yin Theorem 5.17**, stated as
`FubiniStatement.bounded_fubini`. Necessary definition certificates accompany
its vocabulary. Geometric Fubini, monomial decomposition, Puiseux comparisons
and the variety corollary remain in the library.

Two definable maps from finite RV-fibre VF objects have a common mixed VF/RV
base. At every point of that base, actual definable bijections to positive RV
lifts must give equal bounded values over precisely the base point adjoined
to the original ground. The conclusion is equality of the total bounded
invariants. The model, saturation and generated-ground conditions are explicit.
The VF coordinates need not be valuatively bounded.

The independent [Challenge](Challenge.lean) imports Mathlib and Lean's own
compiler modules. It has 990 physical lines and 95,405 bytes, within the
1,000-line and 100-KiB limits. The [Solution](Solution.lean) imports the
substantive proof library and the constructive presentation bridge in
[FubiniStatement](FubiniStatement.lean).

## Definition helpers

The intrinsic reduced RES ring is presented explicitly by actual definable
sets, underlying definable bijections, products, scissors and value-fibre
relations. The Solution proves its ring isomorphism with the original
coefficient presentation.

The bounded RV retraction is specified by bijections, scissors and cylindrical
cell values. The total VF invariant is specified on every actual positive
RV lift. Complete cell decomposition and original-ground lifting, proved in
the Solution, give these specifications their ordinary mathematical meaning.
**Neither construction record contains a Fubini law.**

Each object-construction hole carries its full carrier specification. The
VF field and tuple/quotient presentations are additionally fixed by equations
for their operations, carriers, codes and decoders. The exact inventory and
purposes are recorded in [definition-helpers.json](palomar/definition-helpers.json).
These certificates are statement vocabulary, not additional advertised
research results.

The Challenge also preserves compiler cache boundaries and unfolding-height
metadata. These commands encode no mathematical definition or proof; they
keep the copied declarations mechanically comparable after construction
bodies are supplied by the Solution.

## Verification

The full library build and all 10,566 original public type/axiom comparisons
passed in [GitHub CI](https://github.com/daviddhilbert/Fubini-theorems/actions/runs/44025205470).
The original mathematical sources and public declarations are unchanged.
[The CI receipt](palomar/library-ci.json) identifies that exact snapshot.

The independent pair compiles. Current local and official mechanical evidence,
including its exact source fingerprints and checked commit, is recorded in
[verification.json](palomar/verification.json) and
[readiness.json](palomar/readiness.json). Ordinary library compilation alone
is not a Comparator or independent-kernel check. The full pinned workflow is
[palomar.yml](.github/workflows/palomar.yml).

The [paper](paper/fubini-theorems.tex), its [proof map](paper/PROOF-MAP.json)
and the [blueprint](blueprint/README.md) retain their checked mathematical
source links. Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
