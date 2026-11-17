module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/GammaGroundRVGenerators.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundRVSemiring
public import FubiniTheorems.Prerequisites.Grothendieck.RVGenerators

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gammaGroundRVSpecialCongruence (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    RingCon (GammaGroundRVPositiveSemiring (M := M) hc ground) :=
  ringConGen (fun x y => x = gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (hc := hc) (ground := ground) (rvOneObject ground.real)) ∧
    y = gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (hc := hc) (ground := ground) (rvPositiveObject hc ground.real)) + 1)

def gammaGroundRVPrincipalElement (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    GammaGroundRVGrothendieckRing (M := M) hc ground :=
  Algebra.GrothendieckAddGroup.of (gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (hc := hc) (ground := ground) (rvOneObject ground.real))) -
    Algebra.GrothendieckAddGroup.of (gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (hc := hc) (ground := ground) (rvPositiveObject hc ground.real)))

def gammaGroundRVSpecialCompletionEquiv (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    RingCompletion (gammaGroundRVSpecialCongruence hc ground).Quotient ≃+*
      GammaGroundRVGrothendieckRing hc ground ⧸ Ideal.span ({gammaGroundRVPrincipalElement hc ground - 1} : Set (GammaGroundRVGrothendieckRing hc ground)) :=
  groupifiedUnmeasuredRelation (gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (hc := hc) (ground := ground) (rvOneObject ground.real))) (gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (hc := hc) (ground := ground) (rvPositiveObject hc ground.real)))


end DiamondIntegral.Section3
