/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/GammaGroundFiniteUnions.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import FubiniTheorems.Prerequisites.Grothendieck.GammaGroundDefSets
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {Q : Space LRV M}

theorem GammaGroundDefinable.iUnion {ι : Type} [Finite ι] {A : ι → Set Q.Carrier}
    (hA : ∀ i, GammaGroundDefinable hc ground Q (A i)) :
    GammaGroundDefinable hc ground Q (⋃ i, A i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hf : ∀ f : Finset ι, GammaGroundDefinable hc ground Q {z | ∃ i ∈ f, z ∈ A i} := by
    intro f
    induction f using Finset.induction_on with
    | empty =>
      apply (GammaGroundDefSet.empty hc ground Q).definable.congr
      intro z
      simp [GammaGroundDefSet.empty, GammaGroundDefSet.ofReal, DefSet.empty]
    | @insert i f hi ih =>
      apply ((hA i).union ih).congr
      intro z
      simp
  apply (hf Finset.univ).congr
  intro z
  simp

end DiamondIntegral.Section3
