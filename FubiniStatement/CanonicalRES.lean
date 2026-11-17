module
public import FubiniStatement.NativeObjects
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
namespace FubiniStatement
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Actual finite-value-support RES objects; the label degree is retained
only to encode an object, and is forgotten by the relation below. -/
abbrev RESGenerator (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :=
  Sigma (GammaGroundRESObject hc B)

abbrev RESRaw (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :=
  FreeCommRing (RESGenerator hc B)

def resSymbol {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
    {k : ℕ} (U : GammaGroundRESObject hc B k) : RESRaw hc B := FreeCommRing.of ⟨k,U⟩

/-- A full one-dimensional RV value fibre, specified by its actual carrier. -/
def IsValueLine {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
    {k : ℕ} (U : GammaGroundRESObject hc B k) (α : Values.Gamma (M := M)) : Prop :=
  U.obj.arity = 1 ∧ ∀ u, u ∈ U.obj.domain.carrier ↔ ∀ i, Values.vrv (u i) = α.val

/-- The actual value fibre with its canonical finite-to-one label.
In the independent statement its construction may be left open only together
with the unconditional carrier characterization below. -/
def valueLineWitness (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    (α : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) :
    GammaGroundRESObject hc B 1 :=
  Section3RVChartBridge.nativeRES hc
    (RESFibreObjects.fibre B α 1 hα (GammaGroupNames.one_definable_base B))

theorem valueLineWitness_spec (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    (α : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) :
    IsValueLine (valueLineWitness hc B α hα) α := by
  refine ⟨rfl,?_⟩
  change ∀ u : Fin 1 → CanonicalRV.RVSort M,
    u ∈ (valueLineWitness hc B α hα).obj.domain.carrier ↔ ∀ i, Values.vrv (u i) = α.val
  intro u
  change (Proper (rvValues u) ∧
    GammaRVChartPresentation.codeValues (rvValues u) 0 = α) ↔ _
  constructor
  · rintro ⟨hp,he⟩
    intro i
    fin_cases i
    let t : Code (M := M) := ⟨u 0,(hp 0).2⟩
    have hv := congrArg Subtype.val (codeValue_raw t)
    exact hv.symm.trans (congrArg Subtype.val he)
  · intro h
    have hp : Proper (rvValues u) := by
      intro i
      refine ⟨(u i).property,?_⟩
      intro hz
      exact α.property ((h i).symm.trans ((Values.vrv_eq_infinity_iff (u i)).mpr hz))
    refine ⟨hp,?_⟩
    let t : Code (M := M) := ⟨u 0,(hp 0).2⟩
    have hv := congrArg Subtype.val (codeValue_raw t)
    apply Subtype.ext
    exact hv.trans (h 0)

/-- A genuine full value fibre, with its carrier specification built into
its type. Different finite-to-one labels have the same ungraded class. -/
def valueLineObject (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    (α : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) :
    {U : GammaGroundRESObject hc B 1 // IsValueLine U α} :=
  ⟨valueLineWitness hc B α hα, valueLineWitness_spec hc B α hα⟩

/-- Scissors, products, underlying definable bijections and the value-torsor
relations, over the same original parameter base. -/
inductive RESRelation (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) : RESRaw hc B → Prop
  | unit : RESRelation hc B (resSymbol (resUnit hc B).val - 1)
  | product {k l : ℕ} (U : GammaGroundRESObject hc B k) (V : GammaGroundRESObject hc B l) :
      RESRelation hc B (resSymbol (resProduct U V).val - resSymbol U * resSymbol V)
  | iso {k l : ℕ} (U : GammaGroundRESObject hc B k) (V : GammaGroundRESObject hc B l)
      (e : GammaGroundBijection U.obj.domain V.obj.domain) :
      RESRelation hc B (resSymbol U - resSymbol V)
  | empty {k : ℕ} (U : GammaGroundRESObject hc B k) (h : U.obj.domain.carrier = ∅) :
      RESRelation hc B (resSymbol U)
  | cut {k : ℕ} (U : GammaGroundRESObject hc B k)
      (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.obj.arity))
      (hX : X.carrier ⊆ U.obj.domain.carrier) :
      RESRelation hc B (resSymbol U - resSymbol (resRestrict U X hX).val -
        resSymbol (resRestrict U (U.obj.domain.sdiff X) (fun _ h => h.1)).val)
  | valueLine (α : Values.Gamma (M := M))
      (hα : GammaDefinableClosureAtBase B α) :
      RESRelation hc B (resSymbol (valueLineObject hc B α hα).val -
        resSymbol (valueLineObject hc B 1 (GammaGroupNames.one_definable_base B)).val)

def resIdeal (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) : Ideal (RESRaw hc B) :=
  Ideal.span {r | RESRelation hc B r}

/-- The intrinsic ungraded reduced RES ring of the actual definable sets. -/
abbrev RESRing (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :=
  RESRaw hc B ⧸ resIdeal hc B

def resClass {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
    {k : ℕ} (U : GammaGroundRESObject hc B k) : RESRing hc B :=
  Ideal.Quotient.mk _ (resSymbol U)


variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem resClass_relation (x : RESRaw hc B) (hx : RESRelation hc B x) :
    Ideal.Quotient.mk (resIdeal hc B) x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hx)

theorem resClass_unit : resClass (GammaGroundRESObject.unit hc B) = 1 := by
  have h := resClass_relation _ (RESRelation.unit (hc := hc) (B := B))
  exact sub_eq_zero.mp (by simpa only [resUnit,resClass,map_sub,map_one] using h)

theorem resClass_product {k l : ℕ} (U : GammaGroundRESObject hc B k) (V : GammaGroundRESObject hc B l) :
    resClass (U.product V) = resClass U * resClass V := by
  have h := resClass_relation _ (RESRelation.product U V)
  exact sub_eq_zero.mp (by simpa only [resProduct,rvProduct,resClass,map_sub,map_mul] using h)

theorem resClass_iso {k l : ℕ} (U : GammaGroundRESObject hc B k) (V : GammaGroundRESObject hc B l)
    (e : GammaGroundBijection U.obj.domain V.obj.domain) : resClass U = resClass V := by
  have h := resClass_relation _ (RESRelation.iso U V e)
  exact sub_eq_zero.mp (by simpa only [resClass,map_sub] using h)

theorem resClass_empty {k : ℕ} (U : GammaGroundRESObject hc B k) (h : U.obj.domain.carrier = ∅) :
    resClass U = 0 := resClass_relation _ (RESRelation.empty U h)

theorem resClass_cut {k : ℕ} (U : GammaGroundRESObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.obj.arity))
    (hX : X.carrier ⊆ U.obj.domain.carrier) :
    resClass (U.restrict X hX) + resClass (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)) = resClass U := by
  have h := resClass_relation _ (RESRelation.cut U X hX)
  have h' : resClass U - resClass (U.restrict X hX) -
      resClass (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)) = 0 :=
    by simpa only [resRestrict,resClass,map_sub] using h
  linear_combination -h'

theorem resClass_of_bijection {k l : ℕ} {U : GammaGroundRESObject hc B k} {V : GammaGroundRESObject hc B l}
    (e : GammaGroundBijection U.obj.domain V.obj.domain) : resClass U = resClass V := resClass_iso U V e

namespace Comparison
open DiamondIntegral.Section5

def reducedNative {k : ℕ} (U : GammaGroundRESObject hc B k) : RESDimensionFreeReduction.Ring B :=
  RESDimensionFreeReduction.quotient B (nativeUngradedClass hc U)

theorem reducedNative_native {k : ℕ} (a : RVMeasuredCharts.RESChart B k) :
    reducedNative (Section3RVChartBridge.nativeRES hc a) =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a) := by
  change RESDimensionFreeReduction.fromOrdinary B
    (RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES (Section3RVChartBridge.nativeRES hc a))) = _
  exact congrArg (RESDimensionFreeReduction.fromOrdinary B)
    (RESOrdinaryRing.objectClass_iso (Section3RVRoundtripBridge.chart_native a.toChart))

def rawToOld : RESRaw hc B →+* RESDimensionFreeReduction.Ring B :=
  FreeCommRing.lift (fun a => reducedNative a.2)

theorem rawToOld_symbol {k : ℕ} (U : GammaGroundRESObject hc B k) :
    rawToOld (resSymbol U) = reducedNative U := FreeCommRing.lift_of _ _


theorem rawToOld_relation_zero (x : RESRaw hc B) (hx : RESRelation hc B x) : rawToOld x = 0 := by
  cases hx with
  | unit =>
    rw [map_sub,map_one,rawToOld_symbol]
    simp only [resUnit,reducedNative,nativeUngradedClass_unit,map_one,sub_self]
  | product U V =>
    rw [map_sub,map_mul,rawToOld_symbol,rawToOld_symbol,rawToOld_symbol]
    simp only [resProduct,rvProduct,reducedNative,nativeUngradedClass_product,map_mul,sub_self]
  | iso U V e =>
    rw [map_sub,rawToOld_symbol,rawToOld_symbol]
    exact sub_eq_zero.mpr (congrArg (RESDimensionFreeReduction.quotient B)
      (nativeUngradedClass_bijection hc U V e))
  | @empty k U h =>
    rw [rawToOld_symbol]
    have he := nativeUngradedClass_bijection hc U (GammaGroundRESObject.empty hc B k)
      (GammaGroundBijection.ofEmpty h rfl)
    simp only [reducedNative,he,nativeUngradedClass_empty,map_zero]
  | cut U X hX =>
    simp only [map_sub,rawToOld_symbol]
    have h := congrArg (RESDimensionFreeReduction.quotient B) (nativeUngradedClass_cut hc U X hX)
    simp only [map_add] at h
    change reducedNative U - reducedNative (U.restrict X hX) -
      reducedNative (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)) = 0
    unfold reducedNative
    linear_combination -h
  | valueLine α hα =>
    rw [map_sub,rawToOld_symbol,rawToOld_symbol]
    change reducedNative (Section3RVChartBridge.nativeRES hc
      (RESFibreObjects.fibre B α 1 hα (GammaGroupNames.one_definable_base B))) -
      reducedNative (Section3RVChartBridge.nativeRES hc
        (RESFibreObjects.fibre B 1 1 (GammaGroupNames.one_definable_base B)
          (GammaGroupNames.one_definable_base B))) = 0
    rw [reducedNative_native,reducedNative_native,← map_sub]
    change _ ∈ RingHom.ker (RESDimensionFreeReduction.fromOrdinary B)
    rw [RESDimensionFreeReduction.kernel_fromOrdinary]
    exact (show RESOrdinaryReduction.fibreIdeal B ≤
      RESDimensionFreeRing.degreeIdeal B ⊔ RESOrdinaryReduction.fibreIdeal B from le_sup_right)
      (Ideal.subset_span ⟨α,hα,rfl⟩)

def toOld : RESRing hc B →+* RESDimensionFreeReduction.Ring B :=
  Ideal.Quotient.lift (resIdeal hc B) rawToOld (by
    have hker : resIdeal hc B ≤ RingHom.ker (rawToOld (hc := hc) (B := B)) := by
      apply Ideal.span_le.mpr
      intro x hx
      exact rawToOld_relation_zero x hx
    exact fun _ hx => hker hx)

theorem toOld_class {k : ℕ} (U : GammaGroundRESObject hc B k) :
    toOld (resClass U) = reducedNative U := rawToOld_symbol U


open Section3RESClassCuts Section3RVCodeBridge RVChartDisjointUnion RVChartRestrictions RVAdmissibleFamilies
open RVMeasuredCharts

theorem native_partition {n k : ℕ} (a : Data B n k) (ha : (res B).good k a.toChart)
    (I : Set (Fin n → M)) (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) :
    resClass (ordinaryNative hc a.toChart ha) =
      resClass (ordinaryNative hc (outside a I hI).toChart ((res B).outside_good a I hI ha)) +
        resClass (ordinaryNative hc (inside a I hI).toChart ((res B).inside_good a I hI ha)) := by
  let U := ordinaryNative hc a.toChart ha
  let X := ofRaw (hc := hc) (a.domain ∩ I) (a.domain_definable.inter hI)
  have hX : X.carrier ⊆ U.obj.domain.carrier := fun _ hx => hx.1
  have hi : resClass (U.restrict X hX) =
      resClass (ordinaryNative hc (inside a I hI).toChart ((res B).inside_good a I hI ha)) :=
    resClass_of_bijection (Section3RVRestrictionBridge.nativeRestrictionIso a.toChart _ _ (fun _ hx => hx.1))
  have ho : resClass (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)) =
      resClass (ordinaryNative hc (outside a I hI).toChart ((res B).outside_good a I hI ha)) :=
    resClass_of_bijection (Section3RVClassCuts.complementIso a I hI)
  have h := resClass_cut U X hX
  rw [hi, ho] at h
  exact h.symm.trans (add_comm _ _)


def restrictionInvariant : RVAdmissibleRestrictionInvariants.Ordinary (res B) (RESRing hc B) where
  value _ a ha := resClass (ordinaryNative hc a ha)
  iso _ _ _ _ _ f := resClass_of_bijection (Section3RVRoundtripBridge.nativeIso f)
  partition := native_partition

def chartInvariant : RESOrdinaryRing.Invariant B (RESRing hc B) where
  value _ a := resClass (Section3RVChartBridge.nativeRES hc a)
  unit := (resClass_of_bijection (Section3RVBasicClasses.nativeUnitIso (hc := hc))).trans resClass_unit
  product _ _ a b := by
    rw [← resClass_of_bijection (U := (Section3RVChartBridge.nativeRES hc b).product
      (Section3RVChartBridge.nativeRES hc a)) (V := Section3RVChartBridge.nativeRES hc
        (RVMeasuredProductProperties.resProduct a b))
      (Section3RVBasicClasses.nativeProductIso a.toChart b.toChart),resClass_product]
    exact mul_comm _ _
  iso _ _ _ f := resClass_of_bijection (Section3RVRoundtripBridge.nativeIso f)
  empty _ a ha := by
    apply resClass_empty
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    change rvValues u ∈ a.domain at hu
    exact Set.notMem_empty _ (ha ▸ hu)
  scissor _ a b c d h := RVAdmissibleRestrictionInvariants.ordinary_scissor (res B)
    (restrictionInvariant (hc := hc) (B := B)) a.toChart b.toChart c.toChart d.toChart
      a.finite_values b.finite_values c.finite_values d.finite_values h

def fromChart : RESOrdinaryRing.Ring B →+* RESRing hc B := RESOrdinaryRing.lift B chartInvariant

theorem fromChart_class {k : ℕ} (a : RESChart B k) :
    fromChart (RESOrdinaryRing.objectClass a) = resClass (Section3RVChartBridge.nativeRES hc a) :=
  RESOrdinaryRing.lift_objectClass B chartInvariant a


theorem fromChart_kernel : RingHom.ker (RESDimensionFreeReduction.fromOrdinary B) ≤
    RingHom.ker (fromChart (hc := hc) (B := B)) := by
  rw [RESDimensionFreeReduction.kernel_fromOrdinary]
  apply sup_le
  · apply Ideal.span_le.mpr
    intro x hx
    obtain ⟨k,l,a,b,F,rfl⟩ := hx
    change fromChart (_ - _) = 0
    rw [map_sub,fromChart_class,fromChart_class]
    apply sub_eq_zero.mpr
    exact resClass_of_bijection (bijectionOfRaw a.domain b.domain a.domain_definable b.domain_definable
      F.extension F.extension_graph F.extension_bijOn)
  · apply Ideal.span_le.mpr
    intro x hx
    obtain ⟨α,hα,rfl⟩ := hx
    change fromChart (_ - _) = 0
    rw [map_sub,fromChart_class,fromChart_class]
    have h := resClass_relation _ (RESRelation.valueLine (hc := hc) (B := B) α hα)
    simpa only [resClass,map_sub,valueLineObject,valueLineWitness,RESFibreObjects.torus] using h

theorem fromOrdinary_surjective : Function.Surjective (RESDimensionFreeReduction.fromOrdinary B) := by
  have h1 : Function.Surjective (RESDimensionFreeRing.quotient B) := Ideal.Quotient.mk_surjective
  have h2 : Function.Surjective (RESDimensionFreeReduction.quotient B) := Ideal.Quotient.mk_surjective
  exact h2.comp h1

def fromOld : RESDimensionFreeReduction.Ring B →+* RESRing hc B :=
  (RESDimensionFreeReduction.fromOrdinary B).liftOfSurjective fromOrdinary_surjective
    ⟨fromChart,fromChart_kernel⟩

theorem fromOld_fromOrdinary (x : RESOrdinaryRing.Ring B) :
    fromOld (RESDimensionFreeReduction.fromOrdinary B x) = fromChart (hc := hc) x :=
  RingHom.liftOfSurjective_comp_apply _ fromOrdinary_surjective ⟨fromChart,fromChart_kernel⟩ x

theorem fromOld_toOld (x : RESRing hc B) : fromOld (toOld x) = x := by
  have hh : (fromOld (hc := hc) (B := B)).comp toOld = RingHom.id (RESRing hc B) := by
    apply Ideal.Quotient.ringHom_ext
    apply FreeCommRing.hom_ext
    rintro ⟨k,U⟩
    change fromOld (toOld (resClass U)) = resClass U
    rw [toOld_class]
    change fromOld (RESDimensionFreeReduction.fromOrdinary B
      (RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES U))) = resClass U
    rw [fromOld_fromOrdinary,fromChart_class]
    exact resClass_of_bijection (Section3RVRoundtripBridge.native_chart U.obj)
  exact DFunLike.congr_fun hh x

theorem toOld_fromOld (x : RESDimensionFreeReduction.Ring B) : toOld (fromOld (hc := hc) x) = x := by
  have hh : ((toOld (hc := hc) (B := B)).comp fromOld).comp (RESDimensionFreeReduction.fromOrdinary B) =
      RESDimensionFreeReduction.fromOrdinary B := by
    apply RESOrdinaryRing.hom_ext B
    intro k a
    simp only [RingHom.comp_apply,fromOld_fromOrdinary,fromChart_class,toOld_class,reducedNative_native]
  obtain ⟨y,rfl⟩ := fromOrdinary_surjective (B := B) x
  exact DFunLike.congr_fun hh y

def ringEquiv : RESRing hc B ≃+* RESDimensionFreeReduction.Ring B :=
  { toOld with
    invFun := fromOld
    left_inv := fromOld_toOld
    right_inv := toOld_fromOld }

#print axioms ringEquiv

end Comparison
end FubiniStatement
