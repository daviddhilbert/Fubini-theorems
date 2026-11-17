/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/EmptyGammaSortedDefinability.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import FubiniTheorems.Decomposition.EmptyGammaGround
import FubiniTheorems.Prerequisites.Euler.Section3RVCodeBridge

/-! With no additional imaginary names, the sorted original syntax is
exactly ordinary real-parameter definability with its sort guards. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) {n : ℕ}

include hc in
theorem emptyGamma_sorted_definable_iff (sn : Fin n → SortTag) (A : Set (Fin n → M)) :
    DefinableOverBase (EmptyGammaGround.base S) sn A ↔
      S.Definable LRV A ∧ ∀ x ∈ A,∀ i,sortEval (sn i) (x i) := by
  constructor
  · rintro ⟨k,γ,hγ,hA⟩
    cases k with
    | succ k => exact (hγ 0).elim
    | zero =>
      have hg : γ = Fin.elim0 := funext (fun i => i.elim0)
      subst γ
      have h := (with_zero_iff S Fin.elim0 sn A).mp hA
      rw [definableOver_iff_normalized_raw] at h
      rw [canonical_normalize_eq hc] at h
      exact h
  · intro h
    apply real_definableOverBase
    apply (definableOver_iff_normalized_raw S sn A).mpr
    rw [canonical_normalize_eq hc]
    exact h

theorem emptyGamma_rawDomain_definable
    (D : GammaGroundDefSet hc (EmptyGammaGround.base S) (rawRVSpace (M := M) n)) :
    S.Definable LRV (Section3RVCodeBridge.rawDomain D) :=
  ((emptyGamma_sorted_definable_iff hc S _ _).mp (Section3RVCodeBridge.rawDomain_definable D)).1

end DiamondIntegral.Section5
