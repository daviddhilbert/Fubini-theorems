module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%202/GammaFamilyRestrictions.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Definability.UniformGammaSuprema

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Domain restriction of the complete graph of a Gamma-valued family. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem rawGammaFamilyGraph_restrict_definable (S : Set M)
    (D E : Set (Fin n → M)) (hED : E ⊆ D) (hE : S.Definable LRV E)
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P)) :
    S.Definable LRV (rawGammaFamilyGraph E P) := by
  convert hP.inter (hE.preimage_comp Sum.inl) using 1
  ext z
  constructor
  · rintro ⟨hzE,hzNZ,hzP⟩
    exact ⟨⟨hED hzE,hzNZ,hzP⟩,hzE⟩
  · rintro ⟨⟨_,hzNZ,hzP⟩,hzE⟩
    exact ⟨hzE,hzNZ,hzP⟩

end DiamondIntegral.Section2
