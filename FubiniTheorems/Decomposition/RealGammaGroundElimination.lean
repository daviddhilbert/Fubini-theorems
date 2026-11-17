module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/RealGammaGroundElimination.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Decomposition.EmptyGammaSortedDefinability
public import Section3.GammaClosureLaws

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Gamma names already definable over the real coefficient field can
be eliminated without adjoining an RV representative. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (B : Base (M := M))

theorem realGammaGround_definable_iff
    (hγ : ∀ γ ∈ B.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base B.real) γ)
    {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → M)) :
    DefinableOverBase B sn A ↔ DefinableOverBase (EmptyGammaGround.base B.real) sn A := by
  constructor
  · intro h
    exact h.eliminate_definable_params
      (fun a ha => (subset_closureBase (EmptyGammaGround.base B.real)).1 ha) hγ
  · intro h
    exact h.mono Set.Subset.rfl (Set.empty_subset _)

end DiamondIntegral.Section5
