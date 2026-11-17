/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/PuiseuxAmbientVFFubiniVanishing.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import FubiniTheorems.Comparison.PuiseuxModels.PuiseuxAmbientComparison
import FubiniTheorems.Fubini.NativeVFFubiniVanishing

/-! Bounded VF Fubini vanishing specializes to the actual Puiseux
comparison with the modified equivariant variety ring, over precisely
F = C((t)) in an elementary saturated ambient model. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4
local instance ambientVanishingSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance ambientVanishingSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := N)} {G : GammaGroundContext N}

def ambientBoundedVFVolume
    (e : Carrier ↪ₑ[LRV] N)
    (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := N))
    (H : YinGammaGroundUnmeasuredLiftInput G hc) :
    GammaGroundVFGrothendieckRing hc G.base →+* EquivariantVariety.ModifiedRing :=
  (ambientPuiseuxComparison hc e G.base hB hγ).comp (nativeVFBoundedValue linear H)

theorem ambientBoundedVFVolume_fibre_vanishing
    (e : Carrier ↪ₑ[LRV] N)
    (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := N))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := N) p q))
    (f : GammaGroundMap A.domain C)
    (h : ∀ z ∈ nativeMixedDomain C,NativeBoundedVFFibreLiftVanishing linear A C f z) :
    ambientBoundedVFVolume e hB hγ linear H (nativeVFClass A) = 0 :=
  nativeBoundedVFFubini_vanishing_map linear H A C f h (ambientPuiseuxComparison hc e G.base hB hγ)

end DiamondIntegral.Section5.PuiseuxOriginal
