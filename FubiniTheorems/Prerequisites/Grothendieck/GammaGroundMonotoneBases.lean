/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/d7117c97978deaa2488047cda395266e3a0bc39d/section%203/GammaGroundMonotoneBases.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundMeasuredRVCategories
import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundRealExtensions

/-! Increasing the real and Gamma parameter sets changes only the
proofs of definability. Carriers and complete form functions stay literal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)}
variable {Q R : Space LRV M}

theorem GammaGroundDefinable.monoBase {A : Set Q.Carrier}
    (hA : GammaGroundDefinable hc B Q A) (hr : B.real ⊆ C.real) (hg : B.gamma ⊆ C.gamma) :
    GammaGroundDefinable hc C Q A := by
  obtain ⟨k,γ,hγ,hA⟩ := hA
  exact ⟨k,γ,fun i => hg (hγ i),hA.mono hr⟩

def GammaGroundDefSet.monoBase (A : GammaGroundDefSet hc B Q)
    (hr : B.real ⊆ C.real) (hg : B.gamma ⊆ C.gamma) : GammaGroundDefSet hc C Q :=
  ⟨A.carrier,A.definable.monoBase hr hg⟩

def GammaGroundMap.monoBase {A : GammaGroundDefSet hc B Q} {D : GammaGroundDefSet hc B R}
    (f : GammaGroundMap A D) (hr : B.real ⊆ C.real) (hg : B.gamma ⊆ C.gamma) :
    GammaGroundMap (A.monoBase hr hg) (D.monoBase hr hg) :=
  ⟨f.toFun,f.graph_definable.monoBase hr hg⟩

def gammaGroundVolumeFormMonoBase {A : GammaGroundDefSet hc B Q}
    (ω : GammaGroundVolumeForm hc B A) (hr : B.real ⊆ C.real) (hg : B.gamma ⊆ C.gamma) :
    GammaGroundVolumeForm hc C (A.monoBase hr hg) := ω.monoBase hr hg

end DiamondIntegral.Section3
