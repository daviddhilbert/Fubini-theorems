# Fubini theorems

This repository will contain the active Section 5 results and all local prerequisites from the diamond-integral formalization: monomial decomposition, the canonical Puiseux-model comparison, bounded and geometric Fubini, and the variety corollary.

**Extraction in progress. The proof files have not been moved here yet.** The author requested that the shared-foundation migration pass every affected build and CI run before mathematical extraction begins.

The 106 shared modules are published in [hilbert-mathlib](https://github.com/daviddhilbert/hilbert-mathlib), and all four consumer repositories have updated pins and compatible imports. Local builds and audits pass. The final shared-migration CI checks are running in [integration-in-ACVF](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43920998115) and [diamond-integral](https://github.com/daviddhilbert/diamond-integral/actions/runs/43931987273).

The extraction plan covers 1,786 local proof modules. The checked baseline contains 10,566 public declaration types and axiom inventories; the approved upstream prerequisite promotions have a separate 69-declaration baseline. Original public names and mathematical hypotheses will be retained.

The two former scoped [18] dependency patches have been retired and replaced by the published generated-base kernel through a proved presentation bridge. [The repair CI passed](https://github.com/daviddhilbert/diamond-integral/actions/runs/43904799373).

The subject layout and proof/migration workflow are being initialized. The repository will depend on its pinned upstream libraries and will not depend on diamond-integral.
