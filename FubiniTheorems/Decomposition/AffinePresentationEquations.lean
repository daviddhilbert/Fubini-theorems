module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/AffinePresentationEquations.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Decomposition.AffinePointCoordinates
public import Mathlib.RingTheory.MvPolynomial.Basic

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Every finite-type affine algebra has a finite coordinate presentation
with finitely many kernel equations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
variable (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]

structure FiniteAffineAlgebraPresentation where
  arity : ℕ
  quotient : MvPolynomial (Fin arity) ℂ →ₐ[ℂ] A
  surjective : Function.Surjective quotient
  equations : Finset (MvPolynomial (Fin arity) ℂ)
  kernel : RingHom.ker quotient.toRingHom = Ideal.span (equations : Set (MvPolynomial (Fin arity) ℂ))

theorem finite_affine_algebra_presentation : Nonempty (FiniteAffineAlgebraPresentation A) := by
  obtain ⟨n,φ,hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType ℂ A)
  obtain ⟨s,hs⟩ := (RingHom.ker φ.toRingHom).fg_of_isNoetherianRing
  exact ⟨⟨n,φ,hφ,s,hs.symm⟩⟩

end DiamondIntegral.Section5
