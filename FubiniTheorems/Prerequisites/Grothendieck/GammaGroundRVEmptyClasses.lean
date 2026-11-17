module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/GammaGroundRVEmptyClasses.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundFiniteGluing
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundEmptyBijections
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundRVSemiring
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundCarrierBijections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

def gammaGroundEmptyBijection (P Q : Space LRV M) :
    GammaGroundBijection (GammaGroundDefSet.empty hc B P) (GammaGroundDefSet.empty hc B Q) :=
  ⟨GammaGroundMap.emptyTo _,⟨fun a => False.elim a.property,fun b => False.elim b.property⟩⟩

theorem gammaGroundRVClass_of_empty {k : ℕ} (U : GammaGroundRVObject hc B k) (hU : U.domain.carrier = ∅) :
    gammaGroundRVClass U = 0 := by
  let e : GammaGroundBijection U.domain (GammaGroundDefSet.empty hc B (rawRVSpace U.arity)) :=
    GammaGroundBijection.ofCarrierEq hU
  let f := (gammaGroundEmptyBijection (hc := hc) (B := B) (rawRVSpace U.arity) (rawRVSpace 0)).comp e
  have hi : U ≅ GammaGroundRVObject.empty hc B k := asIso (show _ ⟶ _ from f)
  rw [gammaGroundRVClass_iso hi,gammaGroundRVClass_empty]

theorem gammaGroundRVSemiringClass_of_empty {k : ℕ} (U : GammaGroundRVObject hc B k) (hU : U.domain.carrier = ∅) :
    gammaGroundRVSemiringClass U = 0 := by
  have hh := congrArg (gammaGroundRVKPlusToSemiring (M := M) (hc := hc) (ground := B) (k := k))
    (gammaGroundRVClass_of_empty U hU)
  simpa only [gammaGroundRVKPlusToSemiring_class,map_zero] using hh
end DiamondIntegral.Section3
