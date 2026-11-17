/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/GeometricInverseRingMap.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import FubiniTheorems.Comparison.GeometricPreimageScissors
import FubiniTheorems.Comparison.GeometricPreimageProducts

/-! The inverse value respects every defining geometric relation and
therefore gives an actual inverse-direction ring homomorphism. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical PuiseuxOriginal

def EquivariantVariety.diagonalInvariant : EquivariantVariety.Invariant DiagonalConstructible.Ring where
  value := geometricPreimage
  unit := geometricPreimage_unit
  product := geometricPreimage_product
  iso := fun _ _ f => geometricPreimage_iso f
  empty := geometricPreimage_empty
  scissor := geometricPreimage_scissor

def EquivariantVariety.toDiagonalRing : EquivariantVariety.Ring →+* DiagonalConstructible.Ring :=
  EquivariantVariety.lift EquivariantVariety.diagonalInvariant

theorem EquivariantVariety.toDiagonalRing_objectClass (X : EquivariantVariety.Object) :
    EquivariantVariety.toDiagonalRing (EquivariantVariety.objectClass X) = geometricPreimage X :=
  EquivariantVariety.lift_objectClass EquivariantVariety.diagonalInvariant X

end DiamondIntegral.Section5
