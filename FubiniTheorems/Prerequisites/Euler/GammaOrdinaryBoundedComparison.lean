module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%204/GammaOrdinaryBoundedComparison.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Euler.GammaOrdinaryEvaluation
public import FubiniTheorems.Prerequisites.Euler.GammaBoundedRVProfiles

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The ordinary Euler evaluation on the full Gamma presentation restricts
to the previously constructed bounded ordinary evaluation. The canonical
structure premise is retained exactly for the bounded-profile bridge. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryBoundedComparison
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem evaluation_forget (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    (GammaOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k).comp (GammaBoundedRVMaps.forget B) =
      (GammaBoundedRVProfiles.gradedEvaluation hc h00 linear hκ hs B hr hγ hΓ k).toRingHom := by
  apply GammaBoundedRVPresentation.hom_ext B
  intro n a
  change GammaOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k
    (GammaBoundedRVMaps.forget B (GammaBoundedRVPresentation.objectClass a)) = _
  rw [GammaBoundedRVMaps.forget_class, GammaOrdinaryEvaluation.evaluation_class]
  symm
  change GammaBoundedChartMap.specialize hc h00 linear hκ hs B hr hγ hΓ k (RESOrdinaryReduction.torusClass B)
    (GammaBoundedRVMaps.auxiliary B (GammaBoundedRVPresentation.objectClass a)) = _
  rw [GammaBoundedRVMaps.auxiliary_class]
  exact GammaBoundedChartMap.specialize_boundedClass hc h00 linear hκ hs B hr hγ hΓ k a.toChart a.domain_bounded
    (RESOrdinaryReduction.torusClass B)

end DiamondIntegral.Section4.GammaOrdinaryBoundedComparison
