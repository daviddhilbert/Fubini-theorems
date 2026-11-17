module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/ImmersedProductCoordinateClasses.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Decomposition.AffineImmersedProductPresentations
public import FubiniTheorems.Decomposition.DiagonalGeometricProducts
public import FubiniTheorems.Decomposition.ConstructibleSpectrumObjects
public import FubiniTheorems.Decomposition.DiagonalFinitePartitions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The complex coordinate image of an actual immersed reduced product
is the literal product of its two complex coordinate images. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety PuiseuxOriginal
variable {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ) {Y Z : EquivariantVariety.Object}
variable (f : Morphism Y (rationalAffineObject q)) (g : Morphism Z (rationalAffineObject r))
variable [IsImmersion f.hom] [IsImmersion g.hom]

theorem immersedProduct_coordinate_domain :
    (DiagonalConstructible.immersedObject (Fin.append q r) (affineImmersedProductInclusion q r f g)).domain =
      tupleProductSet (DiagonalConstructible.immersedObject q f).domain (DiagonalConstructible.immersedObject r g).domain := by
  ext z
  change complexTupleSpectrumPoint z ∈ Set.range (affineImmersedProductMap q r f g) ↔
    complexTupleSpectrumPoint (fun i => z (Fin.castAdd m i)) ∈ Set.range f.hom ∧
      complexTupleSpectrumPoint (fun j => z (Fin.natAdd n j)) ∈ Set.range g.hom
  rw [affineImmersedProductMap_range]
  have hL : (rationalAffineLeft q r).hom (complexTupleSpectrumPoint z) =
      complexTupleSpectrumPoint (fun i => z (Fin.castAdd m i)) :=
    complexTupleSpectrumPoint_coordinate (Fin.castAdd m) z
  have hR : (rationalAffineRight q r).hom (complexTupleSpectrumPoint z) =
      complexTupleSpectrumPoint (fun j => z (Fin.natAdd n j)) :=
    complexTupleSpectrumPoint_coordinate (Fin.natAdd n) z
  exact and_congr (Iff.of_eq (congrArg (fun p => p ∈ Set.range f.hom) hL))
    (Iff.of_eq (congrArg (fun p => p ∈ Set.range g.hom) hR))

theorem immersedProduct_coordinate_class :
    DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject (Fin.append q r)
      (affineImmersedProductInclusion q r f g)) =
      DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject q f) *
        DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject r g) := by
  let A := DiagonalConstructible.immersedObject q f
  let B := DiagonalConstructible.immersedObject r g
  let P := DiagonalConstructible.immersedObject (Fin.append q r) (affineImmersedProductInclusion q r f g)
  exact (DiagonalConstructible.setClass_congr (Fin.append q r) P.domain (tupleProductSet A.domain B.domain)
    P.definable P.invariant (DiagonalConstructible.product A B).definable
    (DiagonalConstructible.product A B).invariant (immersedProduct_coordinate_domain q r f g)).trans
      (DiagonalConstructible.objectClass_product A B)

end DiamondIntegral.Section5
