module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/GammaGroundMeasuredRESProducts.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundMeasuredRESScissors
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundMeasuredRVSemiring

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def GammaGroundMeasuredRESObject.product (U : GammaGroundMeasuredRESObject hc ground k)
    (V : GammaGroundMeasuredRESObject hc ground l) : GammaGroundMeasuredRESObject hc ground (k + l) :=
  ⟨U.obj.product V.obj, GammaGroundRVObject.product_res U.property V.property⟩

end DiamondIntegral.Section3
