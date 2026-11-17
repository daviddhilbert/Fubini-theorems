module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/PuiseuxConcreteComparisons.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Comparison.PuiseuxModels.PuiseuxConcreteModel
public import FubiniTheorems.Comparison.GeometricTheta
public import FubiniTheorems.Comparison.PuiseuxModels.PuiseuxInducedRV

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual original-language comparison on the concrete complex
Puiseux model. Its ACVF-model hypothesis is discharged by the checked
Newton–Puiseux and quotient-language constructions. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open DiamondIntegral.Section4
local instance concreteStructure : LRV.Structure Carrier := canonicalInterpret
local instance concreteModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

def canonicalModelPresentation_concrete : PuiseuxModelPresentation Carrier := canonicalModelPresentation

def theta_5_14_concrete :
    RESDimensionFreeReduction.Ring originalPuiseuxGround ≃+* EquivariantVariety.ModifiedRing := theta_5_14

theorem theta_5_14_concrete_mk (x : RESDimensionFreeRing.Ring originalPuiseuxGround) :
    theta_5_14_concrete (RESDimensionFreeReduction.quotient originalPuiseuxGround x) =
      Ideal.Quotient.mk EquivariantVariety.linearActionIdeal (rawVarietyComparison x) := rfl

end DiamondIntegral.Section5.PuiseuxOriginal
