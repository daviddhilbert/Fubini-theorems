module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%204/GammaBoundedRVProfiles.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Euler.GammaBoundedRVMaps
public import FubiniTheorems.Prerequisites.Euler.GammaBoundedRVGrading
public import FubiniTheorems.Prerequisites.Euler.GammaRVGrading
public import FubiniTheorems.Prerequisites.Euler.RESPsiGradings

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual bounded Gamma profile and sharp maps are graded. Their
ordinary RES evaluation is independent of the Euler choice on the entire
intrinsic bounded Gamma presentation. Global RV descent remains open. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedRVProfiles
open GammaBoundedRVCharts GammaBoundedRVPresentation GammaPolynomialGradings
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gradedForget (B : Base (M := M)) :
    GradedRingHom (GammaBoundedRVGrading.gradedPiece B) (GammaRVGrading.gradedPiece B) where
  toRingHom := GammaBoundedRVMaps.forget B
  map_mem := GammaBoundedRVGrading.map_mem_of_classes B (GammaRVGrading.gradingCoaction B)
    (GammaBoundedRVMaps.forget B) (by
      intro n a
      rw [GammaBoundedRVMaps.forget_class]
      exact GammaRVGrading.class_mem B a.toChart)

def gradedSharp (B : Base (M := M)) :
    GradedRingHom (GammaBoundedRVGrading.gradedPiece B) (RVBoundedGrading.gradedPiece B) where
  toRingHom := GammaBoundedRVMaps.sharp B
  map_mem := GammaBoundedRVGrading.map_mem_of_classes B (RVBoundedGrading.gradingCoaction B)
    (GammaBoundedRVMaps.sharp B) (by
      intro n a
      rw [GammaBoundedRVMaps.sharp_class]
      exact RVBoundedGrading.class_mem B _)

def interpretation (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    ChartRing B →+* GammaBoundedPolynomial.sourceRing B k :=
  (GammaBoundedChartMap.interpretation hc h00 linear hκ hs B hr hγ hΓ k).comp (GammaBoundedRVMaps.auxiliary B)

theorem interpretation_class (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ} (a : BoundedChart B n) :
    interpretation hc h00 linear hκ hs B hr hγ hΓ k (objectClass a) =
      GammaBoundedObjectPolynomial.objectPolynomial hc h00 linear hκ hs B hr hγ hΓ k n
        a.support a.support_definable a.toChart.normalizedVolume a.toChart.normalizedVolume_definable a.domain_bounded := by
  change GammaBoundedChartMap.interpretation hc h00 linear hκ hs B hr hγ hΓ k
    (GammaBoundedRVMaps.auxiliary B (objectClass a)) = _
  rw [GammaBoundedRVMaps.auxiliary_class]
  exact GammaBoundedChartMap.interpretation_boundedClass hc h00 linear hκ hs B hr hγ hΓ k a.toChart a.domain_bounded

theorem interpretation_class_mem (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ} (a : BoundedChart B n) :
    interpretation hc h00 linear hκ hs B hr hγ hΓ k (objectClass a) ∈ boundedPiece B k n := by
  rw [interpretation_class]
  exact boundedObjectPolynomial_mem hc h00 linear hκ hs B hr hγ hΓ k n a.support a.support_definable
    a.toChart.normalizedVolume a.toChart.normalizedVolume_definable a.domain_bounded

def gradedInterpretation (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GradedRingHom (GammaBoundedRVGrading.gradedPiece B) (boundedPiece B k) where
  toRingHom := interpretation hc h00 linear hκ hs B hr hγ hΓ k
  map_mem := GammaBoundedRVGrading.map_mem_of_classes B
    (RestrictedPolynomialGrading.coaction (GammaBoundedPolynomial.boundedPointSubring B k))
    (interpretation hc h00 linear hκ hs B hr hγ hΓ k)
    (fun _ a => interpretation_class_mem hc h00 linear hκ hs B hr hγ hΓ k a)

def gradedEvaluation (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GradedRingHom (GammaBoundedRVGrading.gradedPiece B) (RESReductionGradings.ordinaryPiece B) :=
  (RESPsiGradings.gradedBoundedPsi B k).comp (gradedInterpretation hc h00 linear hκ hs B hr hγ hΓ k)

theorem evaluation_independent_kind (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k l : EulerKind) :
    (gradedEvaluation hc h00 linear hκ hs B hr hγ hΓ k).toRingHom =
      (gradedEvaluation hc h00 linear hκ hs B hr hγ hΓ l).toRingHom := by
  apply RingHom.ext
  intro x
  change GammaBoundedChartMap.specialize hc h00 linear hκ hs B hr hγ hΓ k (RESOrdinaryReduction.torusClass B)
      (GammaBoundedRVMaps.auxiliary B x) =
    GammaBoundedChartMap.specialize hc h00 linear hκ hs B hr hγ hΓ l (RESOrdinaryReduction.torusClass B)
      (GammaBoundedRVMaps.auxiliary B x)
  exact RingHom.congr_fun (GammaBoundedChartComparison.specialize_independent_kind
    hc h00 linear hκ hs B hr hγ hΓ k l (RESOrdinaryReduction.torusClass B)) _

end DiamondIntegral.Section4.GammaBoundedRVProfiles
