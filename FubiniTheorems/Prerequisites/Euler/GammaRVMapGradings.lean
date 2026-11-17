module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%204/GammaRVMapGradings.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Euler.GammaRVGrading
public import FubiniTheorems.Prerequisites.Euler.GammaPolynomialGradings
public import FubiniTheorems.Prerequisites.Euler.RVSharpRingMap
public import FubiniTheorems.Prerequisites.Euler.RESPsiGradings

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual Gamma profile maps and sharp map preserve the full grading
of the RV-lift-restricted Gamma presentation. Their composite with psi is
graded; descent from the full RV ring remains a separate obligation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaRVMapGradings
open GammaWeightedCharts GammaRVChartPresentation GammaPolynomialGradings
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gradedSharp (B : Base (M := M)) :
    GradedRingHom (GammaRVGrading.gradedPiece B) (RVGrading.gradedPiece B) where
  toRingHom := RVSharpRingMap.sharp B
  map_mem := GammaRVGrading.map_mem_of_classes B (RVGrading.gradingCoaction B) (RVSharpRingMap.sharp B)
    (fun n a => RVSharpRingMap.sharp_class_mem B a)

theorem interpretation_class_mem (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ} (a : Chart B n) :
    interpretation h00 linear hκ hs B hr hγ hΓ k (objectClass a) ∈ unboundedPiece B k n := by
  change interpretation h00 linear hκ hs B hr hγ hΓ k
    (Ideal.Quotient.mk (relationIdeal B) (GammaChartPresentation.symbol a)) ∈ _
  rw [interpretation_symbol]
  exact objectPolynomial_mem h00 hκ hs B hr hγ k n a.support a.support_definable
    a.normalizedVolume a.normalizedVolume_definable

def gradedInterpretation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GradedRingHom (GammaRVGrading.gradedPiece B) (unboundedPiece B k) where
  toRingHom := interpretation h00 linear hκ hs B hr hγ hΓ k
  map_mem := GammaRVGrading.map_mem_of_classes B
    (RestrictedPolynomialGrading.coaction (GammaPointAlgebra.pointSubring B k))
    (interpretation h00 linear hκ hs B hr hγ hΓ k)
    (fun _ a => interpretation_class_mem h00 linear hκ hs B hr hγ hΓ k a)

def gradedEvaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GradedRingHom (GammaRVGrading.gradedPiece B) (RESReductionGradings.measuredPiece B) :=
  (RESPsiGradings.gradedUnboundedPsi B k).comp (gradedInterpretation h00 linear hκ hs B hr hγ hΓ k)

end DiamondIntegral.Section4.GammaRVMapGradings
