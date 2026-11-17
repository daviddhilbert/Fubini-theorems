/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/GammaGroundRelationPullbacks.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundMapRelations
/-! Pulling a full definable relation back along two actual definable
maps preserves its complete graph over the original parameter set. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language SpecialTransformations.DefinableGeometry
namespace DiamondIntegral.Section3
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

variable {P Q R T : Space LRV M} {rel : Q.Carrier → R.Carrier → Prop}

theorem gammaGroundRelationDefinable_pullback (h : GammaGroundRelationDefinable hc ground Q R rel)
    (f : GammaGroundMap (GammaGroundDefSet.univ hc ground P) (GammaGroundDefSet.univ hc ground Q))
    (g : GammaGroundMap (GammaGroundDefSet.univ hc ground T) (GammaGroundDefSet.univ hc ground R)) :
    GammaGroundRelationDefinable hc ground P T (fun x y => rel (f ⟨x, Set.mem_univ _⟩).val (g ⟨y, Set.mem_univ _⟩).val) := by
  have hd := (f.relation_definable.comp h).comp g.relation_definable.symm
  exact hd.congr (by
    intro x y
    constructor
    · rintro ⟨r, ⟨q, ⟨a, ha, hq⟩, hr⟩, ⟨b, hb, hgr⟩⟩
      have ha' : a = ⟨x, Set.mem_univ _⟩ := Subtype.ext ha
      have hb' : b = ⟨y, Set.mem_univ _⟩ := Subtype.ext hb
      subst a
      subst b
      exact hq.symm ▸ hgr.symm ▸ hr
    · intro hr
      exact ⟨(g ⟨y, Set.mem_univ _⟩).val,
        ⟨(f ⟨x, Set.mem_univ _⟩).val, ⟨⟨x, Set.mem_univ _⟩, rfl, rfl⟩, hr⟩,
        ⟨y, Set.mem_univ _⟩, rfl, rfl⟩)

end DiamondIntegral.Section3
