module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%204/RVTaggedComponentIsomorphisms.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Euler.RVPointProductIsomorphisms
public import FubiniTheorems.Prerequisites.Euler.RVTaggedCoproductClasses

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Each tagged component is actually measured-isomorphic to its
original RV object over the unchanged parameter base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVTaggedComponentIsomorphisms
open RVMeasuredCharts RVMeasuredProduct RVNamedTuples RVPointProductIsomorphisms
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def leftIso {B : Base (M := M)} {k : ℕ} (a b : Chart B k) : Iso (RVTaggedCoproduct.leftData a b).toChart a :=
  RVMeasuredIsomorphisms.trans
    (rightTupleIso (product (tagZero B) a) (fun _ : Fin b.arity => iRVZero) (fun _ => zero_definable B))
    (leftTupleIso B ![iRVZero] (by intro i; fin_cases i; exact zero_definable B) a)

def rightIso {B : Base (M := M)} {k : ℕ} (a b : Chart B k) : Iso (RVTaggedCoproduct.rightData a b).toChart b :=
  RVMeasuredIsomorphisms.trans
    (RVMeasuredIsomorphisms.productIso
      (leftTupleIso B ![iRVOne] (by intro i; fin_cases i; exact one_definable B) (zeros B a.arity))
      (RVMeasuredIsomorphisms.refl b))
    (leftTupleIso B (fun _ : Fin a.arity => iRVZero) (fun _ => zero_definable B) b)

end DiamondIntegral.Section4.RVTaggedComponentIsomorphisms
