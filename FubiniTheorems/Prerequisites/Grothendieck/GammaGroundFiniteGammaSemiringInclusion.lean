/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/GammaGroundFiniteGammaSemiringInclusion.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundFiniteGammaGradedComparison
import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundGammaGradedComparison
import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundFiniteGammaSemiringSquare
/-! The actual finite Gamma inclusion is injective on the positive
semirings as well as on every homogeneous positive component. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

theorem gammaGroundFiniteGammaGradedInclusion_class {k : ℕ} (A : GammaGroundFiniteGammaObject hc ground k) :
    gammaGroundFiniteGammaGradedInclusion (gammaGroundFiniteGammaDirectSumClass A) = gammaGroundGammaDirectSumClass hc A.obj := by
  change DirectSum.map (fun _ => gammaGroundFiniteGammaToGammaKPlus)
    (DirectSum.of (GammaGroundFiniteGammaKPlus hc ground) k (gammaGroundFiniteGammaClass A)) = _
  rw [DirectSum.map_of, gammaGroundFiniteGammaToGammaKPlus_class]
  rfl

theorem gammaGroundFiniteGammaInclusion_grading :
    (gammaGroundGammaPresentationToDirectSum (M := M) (hc := hc) (ground := ground)).comp gammaGroundFiniteGammaToGammaSemiring =
      gammaGroundFiniteGammaGradedInclusion.comp gammaGroundFiniteGammaPresentationToDirectSum := by
  apply PositiveGrothendieck.hom_ext (gammaGroundFiniteGammaSemiringPresentation hc ground)
  rintro ⟨k, A⟩
  change gammaGroundGammaPresentationToDirectSum (gammaGroundFiniteGammaToGammaSemiring (gammaGroundFiniteGammaSemiringClass A)) =
    gammaGroundFiniteGammaGradedInclusion (gammaGroundFiniteGammaPresentationToDirectSum (gammaGroundFiniteGammaSemiringClass A))
  rw [gammaGroundFiniteGammaToGammaSemiring_class, gammaGroundGammaPresentationToDirectSum_class,
    gammaGroundFiniteGammaPresentationToDirectSum_class, gammaGroundFiniteGammaGradedInclusion_class]

theorem gammaGroundFiniteGammaToGammaSemiring_injective :
    Function.Injective (gammaGroundFiniteGammaToGammaSemiring (M := M) (hc := hc) (ground := ground)) := by
  intro a b h
  apply (gammaGroundFiniteGammaSemiringEquivDirectSum (hc := hc) (ground := ground)).injective
  apply gammaGroundFiniteGammaGradedInclusion_injective
  have he := congrArg (gammaGroundGammaPresentationToDirectSum (hc := hc) (ground := ground)) h
  have ha := RingHom.congr_fun (gammaGroundFiniteGammaInclusion_grading (hc := hc) (ground := ground)) a
  have hb := RingHom.congr_fun (gammaGroundFiniteGammaInclusion_grading (hc := hc) (ground := ground)) b
  exact ha.symm.trans (he.trans hb)

end DiamondIntegral.Section3
