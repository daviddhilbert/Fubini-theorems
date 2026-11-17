/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%202/RawFibreRelationalImages.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import FubiniTheorems.Prerequisites.Definability.RawFibreComparisons

/-! Relational images of real fibres, with the source coordinates retained. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] {n : ℕ}

def rawFibreRelationalImage (G : Set (Fin n ⊕ Fin 1 → M)) (R : M → M → Prop) :
    Set (Fin n ⊕ Fin 1 → M) :=
  {z | ∃ y : M, Sum.elim (z ∘ Sum.inl) (fun _ : Fin 1 => y) ∈ G ∧ R y (z (.inr 0))}

theorem rawFibreRelationalImage_definable (S : Set M) (G : Set (Fin n ⊕ Fin 1 → M))
    (hG : S.Definable LRV G) (R : M → M → Prop)
    (hR : S.Definable₂ LRV {p | R p.1 p.2}) : S.Definable LRV (rawFibreRelationalImage G R) := by
  classical
  have h := (rawFibreForallCompare_definable S G hG (fun y u => ¬ R y u) hR.compl).compl
  convert h using 1
  ext z
  change (∃ y, _ ∧ _) ↔ ¬ ∀ y, _ → ¬ _
  simp only [not_forall,not_not,exists_prop]

end DiamondIntegral.Section2
