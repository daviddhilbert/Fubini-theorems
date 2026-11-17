module
public import FubiniStatement.CanonicalRES
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

/-- The full RV inverse image of an actual Gamma set, with no choice of
representatives or valuation section. -/
def gammaLiftDomain {n : ℕ} (T : Set (Fin n → Values.Gamma (M := M))) : Set (Fin n → CanonicalRV.RVSort M) :=
  {u | ∃ γ ∈ T, ∀ i, Values.vrv (u i) = (γ i).val}

theorem sharp_values_iff {n : ℕ} (T : Set (Fin n → Values.Gamma (M := M)))
    (u : Fin n → CanonicalRV.RVSort M) :
    (Proper (rvValues u) ∧ GammaRVChartPresentation.codeValues (rvValues u) ∈ T) ↔ u ∈ gammaLiftDomain T := by
  constructor
  · rintro ⟨hp,hm⟩
    refine ⟨_,hm,?_⟩
    intro i
    let t : Code (M := M) := ⟨u i,(hp i).2⟩
    exact (congrArg Subtype.val (codeValue_raw t)).symm
  · rintro ⟨γ,hγ,he⟩
    have hp : Proper (rvValues u) := by
      intro i
      refine ⟨(u i).property,?_⟩
      intro hz
      exact (γ i).property ((he i).symm.trans ((Values.vrv_eq_infinity_iff (u i)).mpr hz))
    refine ⟨hp,?_⟩
    have hv : GammaRVChartPresentation.codeValues (rvValues u) = γ := by
      funext i
      apply Subtype.ext
      let t : Code (M := M) := ⟨u i,(hp i).2⟩
      exact (congrArg Subtype.val (codeValue_raw t)).trans (he i)
    exact hv ▸ hγ

def gammaLiftWitness (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    {n : ℕ} (T : Set (Fin n → Values.Gamma (M := M))) (hT : GammaOrderLogic.GammaDefinable B T) :
    GammaGroundRVObject hc B n :=
  Section3RVChartBridge.native hc (GammaOrdinaryCharts.sharpChart (GammaOrdinaryCharts.ofSet B n T hT))

theorem gammaLiftWitness_spec (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    {n : ℕ} (T : Set (Fin n → Values.Gamma (M := M))) (hT : GammaOrderLogic.GammaDefinable B T) :
    (gammaLiftWitness hc B T hT).arity = n ∧
      HEq (gammaLiftWitness hc B T hT).domain.carrier (gammaLiftDomain T) := by
  refine ⟨rfl,?_⟩
  apply heq_of_eq
  ext u
  change (Proper (rvValues u) ∧ GammaRVChartPresentation.codeValues (rvValues u) ∈ T) ↔ _
  exact sharp_values_iff T u

/-- A finite-to-one labelled RV representative of the full Gamma inverse
image. Its entire carrier is specified, and the ungraded value forgets labels. -/
def gammaLiftObject (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    {n : ℕ} (T : Set (Fin n → Values.Gamma (M := M))) (hT : GammaOrderLogic.GammaDefinable B T) :
    {U : GammaGroundRVObject hc B n // U.arity = n ∧ HEq U.domain.carrier (gammaLiftDomain T)} :=
  ⟨gammaLiftWitness hc B T hT,gammaLiftWitness_spec hc B T hT⟩

def torusClass (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) : RESRing hc B :=
  resClass (valueLineObject hc B 1 (GammaGroupNames.one_definable_base B)).val

/-- The ordinary bounded RES retraction, characterized by actual underlying
bijections, scissors and monomial cylindrical-cell values. No Fubini law is
part of this definition. -/
structure BoundedRVValues (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) where
  value : ∀ {k : ℕ}, GammaGroundRVObject hc B k → RESRing hc B
  bijection : ∀ {k l : ℕ} (U : GammaGroundRVObject hc B k) (V : GammaGroundRVObject hc B l),
    GammaGroundBijection U.domain V.domain → value U = value V
  empty : ∀ k : ℕ, value (rvEmpty hc B k).val = 0
  cut : ∀ {k : ℕ} (U : GammaGroundRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.arity)) (hX : X.carrier ⊆ U.domain.carrier),
    value (rvRestrict U X hX).val + value (rvRestrict U (U.domain.sdiff X) (fun _ h => h.1)).val = value U
  monomialCell : ∀ {k n : ℕ} (V : GammaGroundRESObject hc B k)
    (T : Set (Fin n → Values.Gamma (M := M))) (shape : CylindricalShape n)
    (hcell : ShapedGammaCell B n T shape),
    value (rvProduct V.obj (gammaLiftObject hc B T hcell.definable).val).val =
      resClass V * torusClass hc B ^ n * (shape.eulerValue .bounded : RESRing hc B)


namespace Construction
open Comparison Section3RVClassCuts
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : DiamondIntegral.Section2.NontrivialDefinableGamma B)

def oldValue {k : ℕ} (U : GammaGroundRVObject hc B k) : RESDimensionFreeReduction.Ring B :=
  nativeGroundRVEvaluation h00 GammaQE.gamma_piecewise_rational_affine hκ hs hc B hr hγ hΓ .bounded (ordinaryClass U)

theorem oldValue_res {k : ℕ} (V : GammaGroundRESObject hc B k) :
    oldValue h00 hκ hs hc B hr hγ hΓ V.obj = reducedNative V := by
  unfold oldValue
  rw [nativeGroundRVEvaluation_class]
  change nativeRVEvaluation h00 GammaQE.gamma_piecewise_rational_affine hκ hs hc B hr hγ hΓ .bounded
    (RVOrdinaryRing.objectClass (Section3RVChartBridge.chartRES V).toChart) =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES V))
  rw [← RVOrdinaryMaps.ofRES_class B (Section3RVChartBridge.chartRES V),nativeRVEvaluation_res]

theorem oldValue_gamma {n : ℕ} (T : Set (Fin n → Values.Gamma (M := M)))
    (shape : CylindricalShape n) (hcell : ShapedGammaCell B n T shape) :
    oldValue h00 hκ hs hc B hr hγ hΓ (gammaLiftObject hc B T hcell.definable).val =
      (shape.eulerValue .bounded : RESDimensionFreeReduction.Ring B) * nativeTorusClass B ^ n := by
  let I := GammaOrdinaryCharts.ofSet B n T hcell.definable
  change oldValue h00 hκ hs hc B hr hγ hΓ (Section3RVChartBridge.native hc (GammaOrdinaryCharts.sharpChart I)) = _
  unfold oldValue
  rw [nativeGroundRVEvaluation_class,
    nativeRVEvaluation_underlyingIso h00 GammaQE.gamma_piecewise_rational_affine hκ hs hc B hr hγ hΓ .bounded
      _ _ (RVUnderlyingIsomorphisms.ofFixed (Section3RVRoundtripBridge.chart_native _)),
    ← GammaOrdinarySharpRingMap.sharp_class B I,nativeRVEvaluation_gamma]
  change (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ .bounded n
    (GammaIndicators.indicatorFamily B T hcell.definable) : RESDimensionFreeReduction.Ring B) *
      nativeTorusClass B ^ n = _
  rw [shaped_cell_euler_value h00 hκ hs B hr hγ .bounded hcell]

theorem inverse_res {k : ℕ} (V : GammaGroundRESObject hc B k) :
    (ringEquiv (hc := hc) (B := B)).symm (reducedNative V) = resClass V := by
  change fromOld (reducedNative V) = resClass V
  rw [← toOld_class V]
  exact fromOld_toOld (resClass V)

theorem inverse_torus : (ringEquiv (hc := hc) (B := B)).symm (nativeTorusClass B) = torusClass hc B := by
  change fromOld (nativeTorusClass B) = _
  rw [show nativeTorusClass B = RESDimensionFreeReduction.fromOrdinary B
    (RESOrdinaryRing.objectClass (RESFibreObjects.torus B)) from
      RESDimensionFreeReduction.fromGradedReduced_raw B _,fromOld_fromOrdinary,fromChart_class]
  rfl

end Construction

/-- The characterized bounded retraction, constructed from the checked native
one and the proved intrinsic-ring comparison. -/
def boundedRVValues (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : DiamondIntegral.Section2.NontrivialDefinableGamma B) : BoundedRVValues hc B where
  value U := (Comparison.ringEquiv (hc := hc) (B := B)).symm (Construction.oldValue h00 hκ hs hc B hr hγ hΓ U)
  bijection U V e := congrArg (Comparison.ringEquiv (hc := hc) (B := B)).symm
    (nativeGroundRVEvaluation_bijection h00 GammaQE.gamma_piecewise_rational_affine hκ hs hc B hr hγ hΓ .bounded U V e)
  empty k := by
    simp only [rvEmpty]
    change (Comparison.ringEquiv (hc := hc) (B := B)).symm
      (nativeGroundRVEvaluation h00 GammaQE.gamma_piecewise_rational_affine hκ hs hc B hr hγ hΓ .bounded
        (Section3RVClassCuts.ordinaryClass (GammaGroundRVObject.empty hc B k))) = 0
    rw [Section3RVClassCuts.ordinary_empty,map_zero,map_zero]
  cut U X hX := by
    have h := congrArg (Comparison.ringEquiv (hc := hc) (B := B)).symm
      (congrArg (nativeGroundRVEvaluation h00 GammaQE.gamma_piecewise_rational_affine hκ hs hc B hr hγ hΓ .bounded)
        (Section3RVClassCuts.ordinary_cut U X hX))
    simpa only [rvRestrict,Construction.oldValue,map_add] using h
  monomialCell V T shape hcell := by
    simp only [rvProduct]
    rw [show Construction.oldValue h00 hκ hs hc B hr hγ hΓ (V.obj.product (gammaLiftObject hc B T hcell.definable).val) =
        Construction.oldValue h00 hκ hs hc B hr hγ hΓ V.obj *
          Construction.oldValue h00 hκ hs hc B hr hγ hΓ (gammaLiftObject hc B T hcell.definable).val from
      nativeGroundRVEvaluation_product h00 GammaQE.gamma_piecewise_rational_affine hκ hs hc B hr hγ hΓ .bounded _ _,
      Construction.oldValue_res h00 hκ hs hc B hr hγ hΓ V,
      Construction.oldValue_gamma h00 hκ hs hc B hr hγ hΓ T shape hcell,
      map_mul,map_mul,map_intCast,map_pow,Construction.inverse_res,Construction.inverse_torus]
    ring

#print axioms boundedRVValues

end FubiniStatement

