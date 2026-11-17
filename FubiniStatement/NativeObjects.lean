module
public import FubiniTheorems.Library
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-- The ordinary Cartesian product carrier, concatenating its RV coordinates. -/
def productCarrier {k l : ℕ} (U : GammaGroundRVObject hc B k) (V : GammaGroundRVObject hc B l) :=
  Set.range (fun x : U.domain × V.domain => Fin.append x.1.val x.2.val)

/-- A labelled Cartesian product, whose entire underlying carrier is fixed. -/
def rvProduct {k l : ℕ} (U : GammaGroundRVObject hc B k) (V : GammaGroundRVObject hc B l) :
    {W : GammaGroundRVObject hc B (k+l) // W.arity = U.arity + V.arity ∧ HEq W.domain.carrier (productCarrier U V)} := by
  refine ⟨U.product V,rfl,?_⟩
  apply heq_of_eq
  ext w
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨⟨⟨a.val.1,a.property.1⟩,⟨a.val.2,a.property.2⟩⟩,rfl⟩
  · rintro ⟨⟨u,v⟩,rfl⟩
    exact ⟨⟨⟨u.val,v.val⟩,u.property,v.property⟩,rfl⟩

/-- A Cartesian product of finite-value-support objects with its full carrier. -/
def resProduct {k l : ℕ} (U : GammaGroundRESObject hc B k) (V : GammaGroundRESObject hc B l) :
    {W : GammaGroundRESObject hc B (k+l) // W.obj.arity = U.obj.arity + V.obj.arity ∧ HEq W.obj.domain.carrier (productCarrier U.obj V.obj)} :=
  ⟨U.product V,(rvProduct U.obj V.obj).property⟩

/-- Restriction to the specified definable subset; no new underlying points. -/
def rvRestrict {k : ℕ} (U : GammaGroundRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.arity)) (hX : X.carrier ⊆ U.domain.carrier) :
    {W : GammaGroundRVObject hc B k // W.arity = U.arity ∧ HEq W.domain.carrier X.carrier} :=
  ⟨U.restrict X hX,rfl,HEq.rfl⟩

/-- Restriction preserves finite value support and has exactly the specified carrier. -/
def resRestrict {k : ℕ} (U : GammaGroundRESObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.obj.arity)) (hX : X.carrier ⊆ U.obj.domain.carrier) :
    {W : GammaGroundRESObject hc B k // W.obj.arity = U.obj.arity ∧ HEq W.obj.domain.carrier X.carrier} :=
  ⟨U.restrict X hX,rfl,HEq.rfl⟩

/-- The zero-dimensional point, the unit of the ungraded RES ring. -/
def resUnit (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    {U : GammaGroundRESObject hc B 0 // U.obj.arity = 0 ∧ HEq U.obj.domain.carrier (Set.univ : Set (Fin 0 → CanonicalRV.RVSort M))} :=
  ⟨GammaGroundRESObject.unit hc B,rfl,HEq.rfl⟩

/-- The empty RV object, with an arbitrary label degree and no underlying points. -/
def rvEmpty (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) :
    {U : GammaGroundRVObject hc B k // U.arity = 0 ∧ HEq U.domain.carrier (∅ : Set (Fin 0 → CanonicalRV.RVSort M))} :=
  ⟨GammaGroundRVObject.empty hc B k,rfl,HEq.rfl⟩
/-- The positive RV lift retains all RV coordinates and imposes precisely
rv(x) = volume(u), over the unchanged parameter base. -/
def vfLift {k : ℕ} (U : GammaGroundRVObject hc B k) :
    {D : GammaGroundDefSet hc B (rawMixedSpace (M := M) k U.arity) //
      D.carrier = {q | ∃ u : U.domain, u.val = q.2 ∧ (U.volume u).val = DiamondIntegral.Section2.tupleRV M q.1}} :=
  ⟨gammaGroundObjectLift U,rfl⟩

/-- The actual map fibre over the raw mixed point, with precisely that tuple
adjoined to the real base and no enlargement of its Gamma parameters. -/
def mapFibre {n r p q : ℕ}
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C)
    (z : Fin (p+q) → M) :
    {D : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawMixedSpace (M := M) n r) //
      D.carrier = {x | ∃ a : A,a.val = x ∧ DiamondIntegral.Section5.nativeMixedCode (f a).val = z}} :=
  ⟨DiamondIntegral.Section5.nativeMixedMapFibreAt f z,Set.ext (DiamondIntegral.Section5.nativeMixedMapFibreAt_mem f z)⟩
end FubiniStatement
