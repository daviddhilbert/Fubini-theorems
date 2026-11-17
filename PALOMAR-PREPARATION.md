# Palomar preparation — Theorem 5.17

**Independent Challenge work remains; this release is not ready for intake.**
The only advertised research result is
`DiamondIntegral.Section5.bounded_fubini_discharged`, Forey–Yin,
*Bounded integral and motivic Milnor fiber*, arXiv:1910.12764v2, Theorem 5.17.
The author permits necessary definition helpers in the Challenge. Geometric
Fubini, Puiseux comparisons and the variety corollary are not separate claims.

## Mathematical scope

Two original-ground definable maps from finite RV-fibre VF objects have a
common finite mixed VF/RV target. At every ambient target point, their fibres
admit actual parameter-definable bijections to RV lifts whose bounded
RES evaluations agree over that same parameter base. The theorem concludes
that the total bounded values agree over the original ground. All ambient
points, including generic points, are tested.

The exact type retains the canonical RV interpretation, ACVF(0,0), an
uncountable saturation bound, strong homogeneity, a small VF-generated real
ground, and a small nontrivial Gamma subgroup containing its RV values.
Nontriviality need not already occur in the VF-generated part. Source objects
have finite RV fibres; their VF coordinates need not be valuatively bounded.
The invariant is bounded Euler reduction of the unmeasured integral.

The [paper](paper/fubini-theorems.tex) gives the mathematical proof. Its
[separate proof map](paper/PROOF-MAP.json) records 19 reviewed steps and 43
Lean declarations. The [blueprint](blueprint/README.md) has 18 nodes and 22
source-linked declarations. Neither document changes the hypotheses.

## Checked module snapshot

The module revision is recorded in `blueprint/proof-source-manifest.json`.
Its pinned providers are published immutable commits, without a dependency
on diamond-integral. All relevant module bodies are exported explicitly.

- `lake build FubiniTheorems`: PASS, 13,021 jobs.
- `python3 verification/verify.py`: PASS, 1,786 implementation modules and
  10,566 unchanged full public types and exact axiom inventories.
- Mathematical-body comparison: PASS, all 1,795 pre-existing Lean files;
  module visibility/import changes preserve the normalized mathematical text.
- Shared foundation: its full library build and all 1,037 unchanged public
  type/axiom comparisons passed. QE: all 85 sources compiled independently;
  the combined headline report matches its baseline byte for byte.
- Blueprint source, anchor, graph and rendered HTML/SVG checks: PASS.
- Paper source-map identity and public-contract coverage: PASS. The compiled
  PDF was rendered and visually reviewed after the bibliography correction.

See `palomar/module-verification.json` for the current source/type receipt,
`palomar/module-migration-source.json` for body hashes and
`palomar/verification.json` for the distinction between current and historical
checks. Only `propext`, `Classical.choice` and `Quot.sound` are accepted.
The current build is distinct from the earlier successful
[extraction CI run](https://github.com/daviddhilbert/Fubini-theorems/actions/runs/43987163120).
Lean 4.35.0 is installed locally outside the default shell PATH.

## Remaining independent submission work

1. Replace the current Challenge's three project imports with faithful
   independent definitions. Its short import-based draft is 50 lines and
   2,583 bytes; that does not satisfy Palomar's import restriction.
   Necessary construction helpers must characterize the actual maps and
   evaluations, rather than leave arbitrary invariants unconstrained.
2. Compile the independent Challenge/Solution pair and run strict Comparator,
   independent NanoDa replay and current official Palomar preflight on the
   same immutable snapshot. None is certified by ordinary library CI.
3. Review the selected statement and metadata, record the public full SHA,
   and use the registry's current intake process if registration is requested.
   No registration, authentication tag/gist or intake has been sent.

The [current guide](https://palomar-registry.org/how-to-submit) and
[binding standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
govern these checks. Read `submit.llms.txt` before driving intake. The current
request authorizes release publication, not registry registration.

## Reproduce

Put the pinned Lean 4.35.0 toolchain on PATH, then run:

```sh
lake build FubiniTheorems
python3 verification/verify.py
python3 scripts/check_paper.py --verified-types
python3 scripts/check_blueprint.py
leanblueprint web
python3 scripts/check_blueprint.py --rendered
python3 scripts/check_palomar.py --output palomar/readiness.json
```

The last command deliberately exits nonzero while the independent Challenge
blocker remains. Its report is a local preparation gate, not official preflight.
The source/type and blueprint workflows follow the other repositories' checked
extraction and submission workflows; their receipts are not Fubini certificates.
