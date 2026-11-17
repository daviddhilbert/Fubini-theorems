module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%204/RVBalancedSpecialGradings.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Euler.RVBalancedGradings
public import FubiniTheorems.Prerequisites.Euler.RVBalancedSpecialClasses

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual P, h and admissible-radius tensor preimages are homogeneous
of degree one. No comparison injectivity is used. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVBalancedSpecialGradings
open RVBalancedGradings RVBalancedSpecialClasses
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem pPreimage_mem (B : Base (M := M)) : pPreimage B ∈ measuredPiece B 1 := by
  unfold pPreimage RVMeasuredSpecialClasses.pPreimage
  rw [map_sub, RVFiniteBalancedTensor.fromInteger_tmul, RVFiniteBalancedTensor.fromInteger_tmul]
  apply (measuredPiece B 1).sub_mem
  · exact measured_tmul_mem B (RESRingCoaction.class_mem_gradedPiece B _) (SetLike.one_mem_graded _)
  · exact measured_tmul_mem B (SetLike.one_mem_graded _) (GammaRVGrading.class_mem B _)

theorem hPreimage_mem (B : Base (M := M)) : hPreimage B ∈ measuredPiece B 1 := by
  unfold hPreimage RVMeasuredSpecialClasses.hPreimage
  rw [RVFiniteBalancedTensor.fromInteger_tmul]
  exact measured_tmul_mem B (SetLike.one_mem_graded _) (GammaRVGrading.class_mem B _)

theorem radiusPreimage_mem (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ GammaRVLifts.admissibleRadii B) : radiusPreimage B γ hγ ∈ boundedPiece B 1 := by
  unfold radiusPreimage RVRadiusTensor.pGammaPreimage RVRadiusTensor.radiusPreimage
  rw [map_sub, map_add, RVBoundedBalancedTensor.fromInteger_tmul,
    RVBoundedBalancedTensor.fromInteger_tmul, RVBoundedBalancedTensor.fromInteger_tmul]
  apply (boundedPiece B 1).sub_mem
  · apply (boundedPiece B 1).add_mem
    · exact bounded_tmul_mem B (SetLike.one_mem_graded _) (GammaBoundedRVGrading.class_mem B _)
    · exact bounded_tmul_mem B (RESRingCoaction.class_mem_gradedPiece B _) (SetLike.one_mem_graded _)
  · exact bounded_tmul_mem B (RESRingCoaction.class_mem_gradedPiece B _) (SetLike.one_mem_graded _)

end DiamondIntegral.Section4.RVBalancedSpecialGradings
