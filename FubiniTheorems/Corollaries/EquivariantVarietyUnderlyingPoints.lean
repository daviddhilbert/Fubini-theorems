/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/EquivariantVarietyUnderlyingPoints.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import FubiniTheorems.Decomposition.ImmersedVarietyFieldPoints
import FubiniTheorems.Decomposition.ComplexAffineCoordinates

/-! Forgetting a finite action retains the actual scheme, coefficient
map and all extension-field points. This connects the geometric affine
partition with the original-complex VF chart coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory

def EquivariantVariety.Object.underlyingVariety (X : EquivariantVariety.Object) : ComplexVariety where
  scheme := X.scheme
  toC := X.toC
  locally_finite_type := X.locally_finite_type
  compact := X.compact
  separated := X.separated
  reduced := X.reduced

def EquivariantVariety.Object.underlyingPointEquiv (X : EquivariantVariety.Object)
    {K : Type} [Field K] [Algebra ℂ K] :
    X.fieldPoint (K := K) ≃ X.underlyingVariety.Point (K := K) := Equiv.refl _

theorem EquivariantVariety.Object.underlyingVariety_isAffine (X : EquivariantVariety.Object)
    [IsAffine X.scheme] : IsAffine X.underlyingVariety.scheme := by
  exact (inferInstance : IsAffine X.scheme)

end DiamondIntegral.Section5
