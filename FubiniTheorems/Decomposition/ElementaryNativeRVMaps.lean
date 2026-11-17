module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/ElementaryNativeRVMaps.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Decomposition.ElementaryNativeRVDomains
public import FubiniTheorems.Fubini.NativeRawGraphMaps
public import FubiniTheorems.Decomposition.RawGraphNativeRealization
public import FubiniTheorems.Decomposition.ElementaryRawGraphBijections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Restriction along an elementary embedding gives actual native RV
maps and bijections over precisely the original named real ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M N P : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
variable (hcM : CanonicalStructure.IsCanonical (M := M)) (hcN : CanonicalStructure.IsCanonical (M := N))
variable (e : M ↪ₑ[LRV] N) (c : P → M) {n m : ℕ}
variable {D : GammaGroundDefSet hcN (EmptyGammaGround.base (Set.range (e ∘ c))) (rawRVSpace (M := N) n)}
variable {E : GammaGroundDefSet hcN (EmptyGammaGround.base (Set.range (e ∘ c))) (rawRVSpace (M := N) m)}

def elementaryNativeRVMap (f : GammaGroundMap D E) :
    GammaGroundMap (elementaryNativeRVRestriction hcM hcN e c D)
      (elementaryNativeRVRestriction hcM hcN e c E) :=
  rawGraphNativeMap hcM c (elementaryNativeRawRestriction_sorted hcN e c D)
    (elementaryNativeRawRestriction_sorted hcN e c E) ((nativeRawGraphMap f).restriction e c)

theorem elementaryNativeRVMap_bijective (f : GammaGroundMap D E) (hf : Function.Bijective f) :
    Function.Bijective (elementaryNativeRVMap hcM hcN e c f) :=
  rawGraphNativeMap_bijective hcM c _ _ _
    ((nativeRawGraphMap f).restrict_bijective e c (nativeRawGraphMap_bijective f hf))

def elementaryNativeRVBijection (f : GammaGroundBijection D E) :
    GammaGroundBijection (elementaryNativeRVRestriction hcM hcN e c D)
      (elementaryNativeRVRestriction hcM hcN e c E) :=
  ⟨elementaryNativeRVMap hcM hcN e c f.map,elementaryNativeRVMap_bijective hcM hcN e c f.map f.bijective⟩

end DiamondIntegral.Section5
