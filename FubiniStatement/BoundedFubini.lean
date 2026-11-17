module
public import FubiniStatement.BoundedValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 DiamondIntegral.Section5
namespace FubiniStatement
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- The bounded invariant of actual finite-RV-fibre VF objects, characterized
by its value on every definable bijection to a positive RV lift. -/
structure BoundedVFValues (G : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M)) where
  value : GammaGroundFiniteVFObject hc G.base → RESRing hc G.base
  lift_value : ∀ (A : GammaGroundFiniteVFObject hc G.base) {k : ℕ}
    (U : GammaGroundRVObject hc G.base k), GammaGroundBijection A.domain (vfLift U).val →
    value A = (boundedRVValues G.model00 G.uncountable.le G.saturated hc G.base G.small_real
      G.small_gamma G.nontrivial_definable_gamma).value U

/-- The canonical bounded invariant, constructed using the original-ground
lifting theorem and the proved intrinsic reduced-RES comparison. -/
def boundedVFValues (G : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M)) :
    BoundedVFValues G hc where
  value A := (Comparison.ringEquiv (hc := hc) (B := G.base)).symm
    (section5BoundedVFIntegral G hc (nativeVFClass A))
  lift_value A _ U e := congrArg (Comparison.ringEquiv (hc := hc) (B := G.base)).symm
    (nativeVFBoundedValue_of_lift_bijection GammaQE.gamma_piecewise_rational_affine
      (completed18GroundLiftInput G hc) A U e)

/-- Equality of the bounded values of two fibres means equality on actual
RV lifts over the original base with precisely the common point adjoined. -/
def FibreLiftEquality (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : DiamondIntegral.Section2.NontrivialDefinableGamma B)
    {n r m s p q : ℕ}
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {A' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}
    (f : GammaGroundMap A C) (f' : GammaGroundMap A' C) (z : Fin (p+q) → M) : Prop :=
  ∃ k l : ℕ,
    ∃ U : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k,
    ∃ V : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ l,
      Nonempty (GammaGroundBijection (mapFibre f z).val (vfLift U).val) ∧
      Nonempty (GammaGroundBijection (mapFibre f' z).val (vfLift V).val) ∧
      (boundedRVValues h00 hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl)).value U =
      (boundedRVValues h00 hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl)).value V

theorem fibreLiftEquality_iff (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : DiamondIntegral.Section2.NontrivialDefinableGamma B)
    {n r m s p q : ℕ}
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {A' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}
    (f : GammaGroundMap A C) (f' : GammaGroundMap A' C) (z : Fin (p+q) → M) :
    FibreLiftEquality h00 hκ hs hr hγ hΓ f f' z ↔
      NativeBoundedVFFibreLiftEquality h00 GammaQE.gamma_piecewise_rational_affine hκ hs hr hγ hΓ f f' z := by
  unfold FibreLiftEquality NativeBoundedVFFibreLiftEquality
  apply exists_congr
  intro k
  apply exists_congr
  intro l
  apply exists_congr
  intro U
  apply exists_congr
  intro V
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  change (Comparison.ringEquiv (hc := hc)).symm (Construction.oldValue h00 hκ hs hc _ _ _ _ U) =
    (Comparison.ringEquiv (hc := hc)).symm (Construction.oldValue h00 hκ hs hc _ _ _ _ V) ↔ _
  rw [(Comparison.ringEquiv (hc := hc)).symm.injective.eq_iff]
  unfold Construction.oldValue
  rw [nativeGroundRVEvaluation_class,nativeGroundRVEvaluation_class]

/-- Forey–Yin Theorem 5.17: equality on every intrinsic parameter-relative
fibre implies equality of the total bounded invariants. -/
theorem bounded_fubini {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M}
    (A A' : GammaGroundFiniteVFObject hc G.base) {p q : ℕ}
    (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C)
    (h : ∀ z ∈ nativeMixedDomain C, FibreLiftEquality G.model00 G.uncountable.le G.saturated G.small_real
      G.small_gamma G.nontrivial_definable_gamma f f' z) :
    (boundedVFValues G hc).value A = (boundedVFValues G hc).value A' := by
  apply congrArg (Comparison.ringEquiv (hc := hc) (B := G.base)).symm
  apply bounded_fubini_discharged A A' C f f'
  intro z hz
  exact (fibreLiftEquality_iff _ _ _ _ _ _ f f' z).mp (h z hz)

#print axioms boundedVFValues
#print axioms bounded_fubini
end FubiniStatement
