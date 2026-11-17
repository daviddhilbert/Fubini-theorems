module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/FunctionalGraphEquivalences.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Decomposition.DiagonalConstructibleRing

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual equivalences constructed from two-sided functional graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
variable {A B : Type*} (R : A → B → Prop)
variable (hA : ∀ a, ∃! b, R a b) (hB : ∀ b, ∃! a, R a b)

def equivalenceOfGraph : A ≃ B :=
  Equiv.ofBijective (fun a => Classical.choose (hA a)) (by
    constructor
    · intro a a' he
      obtain ⟨c, hc, huniq⟩ := hB (Classical.choose (hA a))
      have ha : R a (Classical.choose (hA a)) := (Classical.choose_spec (hA a)).1
      have he' : Classical.choose (hA a) = Classical.choose (hA a') := he
      have ha' : R a' (Classical.choose (hA a)) :=
        Eq.mpr (congrArg (R a') he') (Classical.choose_spec (hA a')).1
      exact (huniq a ha).trans (huniq a' ha').symm
    · intro b
      obtain ⟨a, hab, _⟩ := hB b
      exact ⟨a, ((Classical.choose_spec (hA a)).2 b hab).symm⟩)

theorem equivalenceOfGraph_iff (a : A) (b : B) : R a b ↔ equivalenceOfGraph R hA hB a = b := by
  constructor
  · intro hab
    exact ((Classical.choose_spec (hA a)).2 b hab).symm
  · intro he
    exact he ▸ (Classical.choose_spec (hA a)).1

end DiamondIntegral.Section5
