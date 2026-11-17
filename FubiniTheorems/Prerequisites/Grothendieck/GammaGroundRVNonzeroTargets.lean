module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/GammaGroundRVNonzeroTargets.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundRVDimension
public import FubiniTheorems.Prerequisites.Grothendieck.RVDimensionBridge
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundRVRankUpper
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundRVFiniteMapRank
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundRealization
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundFiniteGluing
public import Section4.RVDimensionRank
public import Section4.GammaRVIndependence
public import Section3.GammaProjection
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundRealFibres
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundMapImages
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundRawDescent
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundSyntaxBridge
public import Section4.RelationFibres

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M}
variable {n : ℕ}
variable {k : ℕ}
theorem gammaGroundRVHasFiniteMap_iff_nonzero
    (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) :
    GammaGroundRVHasFiniteMap A k ↔
      ∃ f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k)),
        f.FiniteFibres ∧ ∀ a i, ((f a).val i).val ≠ iRVZero := by
  constructor
  · rintro ⟨f, hf⟩
    let U := GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k)
    let C : GammaGroundMap U U := GammaGroundMap.ofGlobal _ _
      (cleanRVMap (DefSet.univ (rawRVSpace (M := M) k) ground.real)) (fun _ => Set.mem_univ _)
    have hC : C.FiniteFibres := cleanRVMap_finite (DefSet.univ (rawRVSpace (M := M) k) ground.real)
    refine ⟨C.comp f, hC.comp hf, ?_⟩
    intro a i
    exact cleanRV_nonzero (f a).val i
  · rintro ⟨f, hf, _⟩
    exact ⟨f, hf⟩

end DiamondIntegral.Section3
