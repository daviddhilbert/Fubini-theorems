module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%205/ImmersionBranchGluing.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
public import FubiniTheorems.Decomposition.ReducedAffineBranchGluing
public import FubiniTheorems.Decomposition.ReducedImmersionLifts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Affine immersion branches define a regular map on a reduced
scheme whenever their input images pull back to an open cover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory TopologicalSpace
variable {S T J : Type} [CommRing S] [CommRing T] [Algebra ℂ S] [Algebra ℂ T]
variable {X : Scheme} [AlgebraicGeometry.IsReduced X]
variable (A : J → Type) [∀ j, CommRing (A j)] [∀ j, Algebra ℂ (A j)]
variable [∀ j, Algebra.FiniteType ℂ (A j)] [∀ j, IsReduced (A j)]
variable (f : ∀ j, S →ₐ[ℂ] A j) (base : X ⟶ Spec (.of S))

def immersionBranchOpen (ho : ∀ j, IsOpen {x : X |
    base x ∈ Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))}) (j : J) : X.Opens :=
  ⟨_, ho j⟩

def immersionBranchCover (ho : ∀ j, IsOpen {x : X |
    base x ∈ Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))})
    (hc : ∀ x : X, ∃ j, base x ∈ Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))) :
    X.OpenCover where
  I₀ := J
  X j := (immersionBranchOpen A f base ho j).toScheme
  f j := (immersionBranchOpen A f base ho j).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    obtain ⟨j, hj⟩ := hc x
    exact ⟨j, ⟨⟨x, hj⟩, rfl⟩⟩

def immersionBranchLift
    [∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (f j).toRingHom))]
    (ho : ∀ j, IsOpen {x : X |
      base x ∈ Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))}) (j : J) :
    (immersionBranchOpen A f base ho j).toScheme ⟶ Spec (.of (A j)) :=
  reducedImmersionLift (Spec.map (CommRingCat.ofHom (f j).toRingHom))
    ((immersionBranchOpen A f base ho j).ι ≫ base) (by
      rintro _ ⟨x, rfl⟩
      exact x.property)

theorem immersionBranchLift_fac
    [∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (f j).toRingHom))]
    (ho : ∀ j, IsOpen {x : X |
      base x ∈ Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))}) (j : J) :
    immersionBranchLift A f base ho j ≫ Spec.map (CommRingCat.ofHom (f j).toRingHom) =
      (immersionBranchOpen A f base ho j).ι ≫ base :=
  reducedImmersionLift_fac _ _ _

theorem glue_immersion_branches
    [∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (f j).toRingHom))]
    (a : ∀ j, T →ₐ[ℂ] A j)
    (hc : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp (f i) = ψ.comp (f j) → φ.comp (a i) = ψ.comp (a j))
    (ho : ∀ j, IsOpen {x : X |
      base x ∈ Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))})
    (hcover : ∀ x : X, ∃ j, base x ∈ Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))) :
    ∃! F : X ⟶ Spec (.of T), ∀ j,
      (immersionBranchOpen A f base ho j).ι ≫ F =
        immersionBranchLift A f base ho j ≫ Spec.map (CommRingCat.ofHom (a j).toRingHom) := by
  let 𝒰 := immersionBranchCover A f base ho hcover
  exact glue_reduced_affine_branches 𝒰 A f a hc (immersionBranchLift A f base ho) base
    (immersionBranchLift_fac A f base ho)

end DiamondIntegral.Section5
