/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/ComplexAffineCoordinates.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import FubiniTheorems.Decomposition.ComplexVarietyAffinePoints

/-! Every actual affine complex variety has finite kernel equations,
and all extension-field scheme points have those precise coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] ComplexVariety.coordinateAlgebra

instance ComplexVariety.coordinateAlgebra_finiteType (X : ComplexVariety) [IsAffine X.scheme] :
    Algebra.FiniteType ℂ Γ(X.scheme, ⊤) := by
  letI : LocallyOfFiniteType X.toC := X.locally_finite_type
  have hFT : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.scheme, ⊤)))) := by
    rw [X.coordinateSpec_toC]
    infer_instance
  exact RingHom.finiteType_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hFT)

theorem ComplexVariety.affine_coordinate_presentation (X : ComplexVariety) [IsAffine X.scheme] :
    Nonempty (FiniteAffineAlgebraPresentation Γ(X.scheme, ⊤)) := finite_affine_algebra_presentation _

def ComplexVariety.affineCoordinates (X : ComplexVariety) [IsAffine X.scheme]
    {K : Type} [Field K] [Algebra ℂ K] (P : FiniteAffineAlgebraPresentation Γ(X.scheme, ⊤)) :
    X.Point (K := K) ≃ {x : Fin P.arity → K | ∀ p ∈ P.equations,MvPolynomial.aeval x p = 0} :=
  X.affinePointEquiv.trans (finiteAffinePointEquiv P)

end DiamondIntegral.Section5
