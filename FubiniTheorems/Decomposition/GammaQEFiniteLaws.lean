/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/GammaQEFiniteLaws.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import Section3.GammaQEFiniteLaws
import Section3.GammaQEGraphCritical
import HilbertMathlib.Foundation.Euler.GammaQEPositiveLaw
import FubiniTheorems.Prerequisites.Definability.CitedGammaLinearity

/-! The exact unary Gamma rational-affine input is proved from original
RV quantifier elimination. No saturation or additional parameters occur. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiamondIntegral.Section5.GammaQE
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open CanonicalRV GuardedRVNormalForm
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {I R : Type}

theorem gamma_piecewise_rational_affine : Section2.GammaPiecewiseRationalAffineInput (M := M) := by
  intro h00 S hΓ D f hf
  obtain ⟨I,R,a,r,N,hN⟩ := gamma_flat_normal_form S
    (fun z : Fin 2 → Values.Gamma (M := M) => z 0 ∈ D ∧ f (z 0) = z 1) hf
  exact finite_laws_of_flat_graph a r N D f hN

end DiamondIntegral.Section5.GammaQE
