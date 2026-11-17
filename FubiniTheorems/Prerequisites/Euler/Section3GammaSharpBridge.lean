module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%204/Section3GammaSharpBridge.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Euler.Section3GammaRVCodeBridge
public import FubiniTheorems.Prerequisites.Euler.Section3RVRingEquivalences
public import FubiniTheorems.Prerequisites.Euler.Section3GammaChartBridge
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundMeasuredGammaRVLift

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The chart sharp construction agrees with the native full RV-code
lift. The explicit one-piece tag is transported by a genuine bijection. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaSharpBridge
open Section3GammaCodeBridge Section3GammaRVCodeBridge Section3GammaChartBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def ordinary {n : ℕ} (a : GammaOrdinaryCharts.Chart B n) :
    GammaGroundBijection (Section3RVChartBridge.native hc (GammaOrdinaryCharts.sharpChart a)).domain
      (nativeOrdinary hc a).rvLift.domain :=
  (gammaGroundGammaSingleLiftBijection (native hc a.support a.support_definable)).comp
    (GammaGroundBijection.ofCarrierEq (codeLift_carrier (native hc a.support a.support_definable))).symm

theorem ordinary_code {n : ℕ} (a : GammaOrdinaryCharts.Chart B n)
    (c : gammaGroundCodePreimage (native hc a.support a.support_definable)) :
    (ordinary (hc := hc) a).map ((codeBijection (native hc a.support a.support_definable)).map c) =
      (nativeOrdinary hc a).rvEncodeCode ⟨(0 : Fin 1), c⟩ := by
  let G := native hc a.support a.support_definable
  let E := GammaGroundBijection.ofCarrierEq (codeLift_carrier G)
  exact congrArg (gammaGroundGammaSingleLiftBijection G).map
    (E.symm_apply_apply ((gammaGroundGammaRVCodeBijection G).map c))

def measured {n : ℕ} (a : GammaWeightedCharts.Chart B n) :
    GammaGroundMeasuredRVHom (Section3MeasuredRVChartBridge.native hc (RVSharpCharts.sharpChart a))
      (nativeMeasured hc a).rvLift where
  bijection := ordinary (GammaOrdinaryCharts.ofWeighted a)
  preserves u := by
    obtain ⟨c, rfl⟩ := (codeBijection (native hc a.support a.support_definable)).bijective.2 u
    have he := ordinary_code (hc := hc) (GammaOrdinaryCharts.ofWeighted a) c
    have hw := gammaGroundMeasuredGammaLift_combined (nativeMeasured hc a) ⟨(0 : Fin 1), c⟩
    calc
      _ = (nativeMeasured hc a).combinedWeight ((nativeMeasured hc a).underlying.decode ⟨(0 : Fin 1), c⟩) := by
        rw [Section3MeasuredRVChartBridge.native_weight, nativeMeasured_weight,
          codeBijection_value, RVSharpCharts.sharpChart_weight, rawCode_value]
        rfl
      _ = (nativeMeasured hc a).rvLift.combinedWeight ((nativeMeasured hc a).underlying.rvEncodeCode ⟨(0 : Fin 1), c⟩) := hw.symm
      _ = _ := congrArg (nativeMeasured hc a).rvLift.combinedWeight he.symm

end DiamondIntegral.Section4.Section3GammaSharpBridge
