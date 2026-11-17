module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/CoordinateProductChart.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Definability.ZeroFaces

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {n : ℕ} {Z : Set (Fin n)} {α : Type}

def coordinateProductChart (C : Section2.ZeroFaceChart Z) :
    (Fin n → α) ≃ (Fin C.zeroArity → α) × (Fin C.freeArity → α) :=
  (Equiv.arrowCongr C.coordinates.symm (Equiv.refl α)).trans (Fin.appendEquiv C.zeroArity C.freeArity).symm

theorem coordinateProductChart_fst (C : Section2.ZeroFaceChart Z) (x : Fin n → α) (i : Fin C.zeroArity) :
    (coordinateProductChart C x).1 i = x (C.zeroIndex i) := rfl

theorem coordinateProductChart_snd (C : Section2.ZeroFaceChart Z) (x : Fin n → α) (i : Fin C.freeArity) :
    (coordinateProductChart C x).2 i = x (C.freeIndex i) := rfl

theorem coordinateProductChart_fixed_cover (C : Section2.ZeroFaceChart Z) (j : Fin n) (hj : j ∈ Z) :
    ∃ i, j = C.zeroIndex i := by
  rcases C.coordinate_cases j with hh | ⟨i,rfl⟩
  · exact hh
  · exact (C.free_not_mem i hj).elim

theorem coordinateProductChart_free_cover (C : Section2.ZeroFaceChart Z) (j : Fin n) (hj : j ∉ Z) :
    ∃ i, j = C.freeIndex i := by
  rcases C.coordinate_cases j with ⟨i,rfl⟩ | hh
  · exact (hj (C.zero_mem i)).elim
  · exact hh
end DiamondIntegral.Section3
