/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/AffinePointFiniteEquations.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import FubiniTheorems.Decomposition.AffinePresentationEquations

/-! Actual points of each affine chart are cut out by its finite list of
kernel equations. This is the finite presentation used for VF formulas. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
variable {A K : Type} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
variable [Field K] [Algebra ℂ K]

theorem finiteAffinePoint_equations_iff (P : FiniteAffineAlgebraPresentation A) (x : Fin P.arity → K) :
    RingHom.ker P.quotient.toRingHom ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom ↔
      ∀ p ∈ P.equations,MvPolynomial.aeval x p = 0 := by
  rw [P.kernel,Ideal.span_le]
  rfl

def finiteAffinePointEquiv (P : FiniteAffineAlgebraPresentation A) :
    (A →ₐ[ℂ] K) ≃ {x : Fin P.arity → K | ∀ p ∈ P.equations,MvPolynomial.aeval x p = 0} :=
  (affinePointCoordinateEquiv P.quotient P.surjective).trans
    (Equiv.subtypeEquivRight (fun x => finiteAffinePoint_equations_iff P x))

end DiamondIntegral.Section5
