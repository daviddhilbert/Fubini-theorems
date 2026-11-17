module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/GammaRVLift.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Prerequisites.Grothendieck.GammaRVCodeLift
public import FubiniTheorems.Prerequisites.Grothendieck.FamilyPieceMaps
public import FubiniTheorems.Prerequisites.Grothendieck.RVFamilyObjects

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual Gamma-to-RV object lift for every finite tagged family.
A Gamma arrow supplies a genuine RV isomorphism of these lifts. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def GammaObject.rvPieces (A : GammaObject hc S k) : FiniteFamily (rawRVSpace k) S :=
  ⟨A.tags, fun i => (gammaRVCodeLift (A.piece i)).domain⟩

def GammaObject.rvCodeBijection (A : GammaObject hc S k) :
    FamilyBijection A.codeLift A.rvPieces :=
  FamilyBijection.pieces A.codeLift _ (fun i => gammaRVCodeBijection (A.piece i))

theorem GammaObject.rvPieces_nonzero (A : GammaObject hc S k)
    (i : Fin A.rvPieces.tags) (a : A.rvPieces.piece i) (j : Fin k) :
    (a.val j).val ≠ iRVZero := (gammaRVCodeLift (A.piece i)).nonzero a j

def GammaObject.rvLift (A : GammaObject hc S k) : RVObject S k :=
  A.rvPieces.rvObject A.rvPieces_nonzero

theorem gammaHom_lift_iso {A B : GammaObject hc S k} (f : A ⟶ B) :
    Nonempty (A.rvLift ≅ B.rvLift) := by
  obtain ⟨F, _⟩ := f.contraction
  exact ⟨rvFamilyIso A.rvPieces_nonzero B.rvPieces_nonzero
    (B.rvCodeBijection.comp (F.comp A.rvCodeBijection.symm))⟩

end DiamondIntegral.Section3
