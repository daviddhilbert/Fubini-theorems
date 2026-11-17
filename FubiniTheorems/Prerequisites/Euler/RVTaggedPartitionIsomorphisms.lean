/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%204/RVTaggedPartitionIsomorphisms.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import FubiniTheorems.Prerequisites.Euler.RVTaggedComponentIsomorphisms
import FubiniTheorems.Prerequisites.Euler.RVDisjointUnionIsomorphisms
import FubiniTheorems.Prerequisites.Euler.RVChartRestrictions

/-! A tagged disjoint union is actually measured-isomorphic to an
already-disjoint common-arity union. In particular, the tagged union of
the two definable pieces of a partition is isomorphic to the original
object. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVTaggedPartitionIsomorphisms
open RVMeasuredCharts RVChartDisjointUnion RVChartRestrictions
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def disjointTaggedIso {B : Base (M := M)} {n k : ℕ} (a b : Data B n k) (hab : Disjoint a.domain b.domain) :
    Iso (RVTaggedCoproduct.coproduct a.toChart b.toChart) (disjointUnion a b hab).toChart :=
  RVDisjointUnionIsomorphisms.unionIso
    (RVTaggedCoproduct.leftData a.toChart b.toChart) (RVTaggedCoproduct.rightData a.toChart b.toChart) a b
    (RVTaggedCoproduct.tagged_disjoint a.toChart b.toChart) hab
    (RVTaggedComponentIsomorphisms.leftIso a.toChart b.toChart)
    (RVTaggedComponentIsomorphisms.rightIso a.toChart b.toChart)

def partitionTaggedIso {B : Base (M := M)} {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) :
    Iso (RVTaggedCoproduct.coproduct (outside a I hI).toChart (inside a I hI).toChart) a.toChart :=
  RVMeasuredIsomorphisms.trans
    (disjointTaggedIso (outside a I hI) (inside a I hI) (pieces_disjoint a I hI)) (partitionIso a I hI)

end DiamondIntegral.Section4.RVTaggedPartitionIsomorphisms
