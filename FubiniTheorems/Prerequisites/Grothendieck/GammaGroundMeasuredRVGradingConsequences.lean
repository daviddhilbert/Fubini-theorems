module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/GammaGroundMeasuredRVGradingConsequences.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundMeasuredRVGradedComparison
public import FubiniTheorems.Prerequisites.Grothendieck.CompletionDirectSum
public import FubiniTheorems.Prerequisites.Grothendieck.CompletionEquivalences
public import FubiniTheorems.Prerequisites.Grothendieck.PresentationHomExt

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual fixed-degree inclusions and group gradings after the checked
Gamma-ground RV semiring/direct-sum comparison. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundMeasuredRVPresentationToDirectSum_fixed (a : GammaGroundMeasuredRVKPlus hc ground k) :
    gammaGroundMeasuredRVPresentationToDirectSum (gammaGroundMeasuredRVKPlusToSemiring a) = DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) k a := by
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredRVClass_surjective a
  rw [gammaGroundMeasuredRVKPlusToSemiring_class, gammaGroundMeasuredRVPresentationToDirectSum_class]
  rfl

theorem gammaGroundMeasuredRVKPlusToSemiring_injective :
    Function.Injective (gammaGroundMeasuredRVKPlusToSemiring (hc := hc) (ground := ground) (k := k)) := by
  intro a b hab
  have he := congrArg (gammaGroundMeasuredRVPresentationToDirectSum (hc := hc) (ground := ground)) hab
  rw [gammaGroundMeasuredRVPresentationToDirectSum_fixed, gammaGroundMeasuredRVPresentationToDirectSum_fixed] at he
  have ht := congrArg (fun z : GammaGroundMeasuredRVDirectSum hc ground => z k) he
  simpa only [DirectSum.of_eq_same] using ht

def gammaGroundMeasuredRVGroupDirectSumEquiv : GammaGroundMeasuredRVGrothendieckRing hc ground ≃+
    DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (GammaGroundMeasuredRVKPlus hc ground k)) :=
  (ringCompletionCongr (gammaGroundMeasuredRVSemiringEquivDirectSum (hc := hc) (ground := ground))).toAddEquiv.trans
    (completionDirectSumEquiv (GammaGroundMeasuredRVKPlus hc ground))

@[simp] theorem gammaGroundMeasuredRVGroupDirectSumEquiv_class (U : GammaGroundMeasuredRVObject hc ground k) :
    gammaGroundMeasuredRVGroupDirectSumEquiv (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass U)) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (GammaGroundMeasuredRVKPlus hc ground k)) k
        (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVClass U)) := by
  change completionDirectSumEquiv (GammaGroundMeasuredRVKPlus hc ground)
    (ringCompletionCongr (gammaGroundMeasuredRVSemiringEquivDirectSum (hc := hc) (ground := ground))
      (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass U))) = _
  rw [ringCompletionCongr_of]
  simp only [gammaGroundMeasuredRVSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, gammaGroundMeasuredRVPresentationToDirectSum_class]
  exact completionDirectSumEquiv_of (GammaGroundMeasuredRVKPlus hc ground) k (gammaGroundMeasuredRVClass U)

end DiamondIntegral.Section3
