module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/GammaGroundGraphSets.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundMapProducts
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundBijections

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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M} {A : GammaGroundDefSet hc B P} {D : GammaGroundDefSet hc B Q}

def GammaGroundMap.graphSet (f : GammaGroundMap A D) : GammaGroundDefSet hc B (P.prod Q) :=
  ⟨{z | ∃ a : A, a.val = z.1 ∧ (f a).val = z.2},f.graph_definable⟩

def GammaGroundMap.graphPair (f : GammaGroundMap A D) : GammaGroundMap A f.graphSet :=
  ((GammaGroundMap.id A).pair f).corestrict (fun a => ⟨a,rfl,rfl⟩)

theorem GammaGroundMap.graphPair_bijective (f : GammaGroundMap A D) : Function.Bijective f.graphPair := by
  constructor
  · intro a b hab
    exact Subtype.ext (congrArg (fun z : f.graphSet => z.val.1) hab)
  · rintro ⟨z,a,ha,hf⟩
    exact ⟨a,Subtype.ext (Prod.ext ha hf)⟩

def GammaGroundMap.graphPairBijection (f : GammaGroundMap A D) : GammaGroundBijection A f.graphSet :=
  ⟨f.graphPair,f.graphPair_bijective⟩
end DiamondIntegral.Section3
