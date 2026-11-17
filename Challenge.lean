module
public import FubiniTheorems.Fubini.Completed18GroundLiftInput
public import FubiniTheorems.Decomposition.GammaQEFiniteLaws
public import FubiniTheorems.Fubini.NativeVFFubini
@[expose] public section
/-!
# Theorem 5.17 — bounded Fubini (preparation draft)

This file states only the main Fubini result. For each point of a common
mixed VF/RV base, the two fibres must admit parameter-definable RV lifts
with equal bounded RES evaluations. The conclusion is equality of the
bounded invariants of the two total VF classes.

The canonical ACVF(0,0) model, genuine saturation, strong homogeneity,
small VF/Gamma ground and finite RV-fibre conditions remain in the type.
The two construction inputs are supplied by proved declarations.

PREPARATION ONLY: these project imports violate Palomar's independent
Challenge import rule. Replace them by a faithful, self-contained
statement vocabulary over allowlisted libraries, within the Challenge
size limits. No Comparator or fresh Lean check is claimed for this file.
See PALOMAR-PREPARATION.md and palomar/readiness.json.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M}

def section5BoundedVFIntegral (G : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M)) :=
  nativeVFBoundedValue GammaQE.gamma_piecewise_rational_affine (completed18GroundLiftInput G hc)


/-- Forey–Yin, Theorem 5.17, with the original exported hypotheses. -/
theorem bounded_fubini_discharged (A A' : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C)
    (h : ∀ z∈nativeMixedDomain C,NativeBoundedVFFibreLiftEquality G.model00
      GammaQE.gamma_piecewise_rational_affine G.uncountable.le G.saturated G.small_real
      G.small_gamma G.nontrivial_definable_gamma f f' z) :
    section5BoundedVFIntegral G hc (nativeVFClass A)=section5BoundedVFIntegral G hc (nativeVFClass A') := by
  sorry

end DiamondIntegral.Section5
