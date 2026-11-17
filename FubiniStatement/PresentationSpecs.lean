module
public import FubiniStatement.NativeObjects
@[expose] public section
noncomputable section
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
namespace FubiniStatement
/-- The complete carrier, code sort, code domain and decoding function of a
presentation. Definability and surjectivity certificates are proof fields. -/
def spaceData {L : Language} {M : Type} [L.Structure M] (P : SpecialTransformations.DefinableGeometry.Space L M) :
    (X : Type) × (ι : Type) × (D : Set (ι → M)) × (D → X) :=
  ⟨P.Carrier,P.Index,P.domain,P.decode⟩
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
/-- Gamma has all nonzero RV codes and decodes by the actual value quotient. -/
theorem gammaSpace_data : @spaceData LRV M (CanonicalStructure.normalize (M := M)) (gammaSpace (M := M)) =
    ⟨Values.Gamma (M := M),Fin 1,{z | iRV (z 0) ∧ z 0 ≠ iRVZero},
      fun z => Values.gammaOf ⟨z.val 0,z.property.1⟩ z.property.2⟩ := rfl
/-- Raw VF coordinates are coded by their underlying original-model elements. -/
theorem rawVFSpace_data (n : ℕ) : spaceData (rawVFSpace (M := M) n) =
    ⟨Fin n → VFType (M := M),Fin n,Set.range (vfValues (M := M) (n := n)),fun z => Classical.choose z.property⟩ := rfl
/-- Raw RV coordinates have exactly the original RV-sort tuple carrier. -/
theorem rawRVSpace_data (n : ℕ) : spaceData (rawRVSpace (M := M) n) =
    ⟨Fin n → CanonicalRV.RVSort M,Fin n,Set.range (rvValues (M := M) (n := n)),fun z => Classical.choose z.property⟩ := rfl
/-- The VF field structure is the original model's zero, one, addition and
multiplication. Field laws determine its remaining operations uniquely. -/
theorem vfField_operations :
    let F := vfFieldOfModel (M := M)
    F.zero.val = iVFZero ∧ F.one.val = iVFOne ∧
      (∀ a b, (F.add a b).val = iVFAdd a.val b.val) ∧
      (∀ a b, (F.mul a b).val = iVFMul a.val b.val) := by
  exact ⟨rfl,rfl,fun _ _ => rfl,fun _ _ => rfl⟩
open CategoryTheory DiamondIntegral.Section3 SpecialTransformations.Section3.GammaParameters
/-- The category decoration of RES objects has exactly the actual underlying
definable bijections as its morphisms; labels are forgotten. -/
theorem rvGroupoid_hom {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
    (U V : GammaGroundRVObject hc B k) : (U ⟶ V) = GammaGroundBijection U.domain V.domain := rfl
end FubiniStatement
