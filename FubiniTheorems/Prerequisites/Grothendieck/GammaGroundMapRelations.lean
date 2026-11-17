module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/GammaGroundMapRelations.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundRelations
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundRawGraphs

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M} {A : GammaGroundDefSet hc ground P} {B : GammaGroundDefSet hc ground Q}

theorem GammaGroundMap.relation_definable (f : GammaGroundMap A B) :
    GammaGroundRelationDefinable hc ground P Q f.graph := f.graph_definable

end DiamondIntegral.Section3
