module
public import Mathlib
meta import all Lean.Meta.Match.Match
meta import Lean.Meta.Tactic.AuxLemma
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.privateInPublic true
set_option backward.proofsInPublic true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section
/- Preserve the original module boundaries of two compiler-only caches.
   Otherwise Lean reuses a matcher from an earlier copied file and changes
   declaration names. This clears caches, not mathematical declarations. Constructor holes also
   retain their original compiler unfolding priorities through height overrides;
   these integers specify no mathematical values or proofs. -/
open Lean Elab Command
elab "reset_statement_module_caches" : command => do
  let cache : Name := `_private.Lean.Meta.Match.Match ++ .num .anonymous 0 ++ `Lean.Meta.Match.matcherExt
  unless (← getEnv).contains cache do throwError "Pinned Lean matcher cache is unavailable"
  elabCommand (← `(command| run_cmd do
    Lean.modifyEnv (fun env => Lean.EnvExtension.modifyState $(mkIdent cache)
      (Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})) (fun _ => {}))))
/-!
# Bounded Fubini — Forey–Yin Theorem 5.17
Only bounded Fubini is the advertised research result. Construction helpers
specify actual carriers, parameter bases and the bounded Euler retraction.
The independent vocabulary uses the intrinsic reduced RES ring; the Solution
proves its equivalence with the original ring and transports the original
theorem without changing any model, ground or fibre-lift hypothesis.
-/
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language
namespace SpecialTransformations.DefinableGeometry
variable {L : Language} {M : Type} [L.Structure M]
structure Space (L : Language) (M : Type) [L.Structure M] where
  Carrier : Type
  Index : Type
  finiteIndex : Finite Index
  domain : Set (Index → M)
  domain_definable : (∅ : Set M).Definable L domain
  decode : domain → Carrier
  onto : Function.Surjective decode
  diagonal_definable : (∅ : Set M).Definable L {z : Index ⊕ Index → M | ∃ hx : z ∘ Sum.inl ∈ domain, ∃ hy : z ∘ Sum.inr ∈ domain, decode ⟨z ∘ Sum.inl, hx⟩ = decode ⟨z ∘ Sum.inr, hy⟩}
attribute [instance] Space.finiteIndex
namespace Space
variable (P Q R : Space L M)
def preimage (A : Set P.Carrier) : Set (P.Index → M) := {z | ∃ hz : z ∈ P.domain, P.decode ⟨z, hz⟩ ∈ A}
def Definable (S : Set M) (A : Set P.Carrier) : Prop := S.Definable L (P.preimage A)
theorem definable_univ (S : Set M) : P.Definable S Set.univ := by sorry
end Space
namespace Space
variable (P Q : Space L M)
/-- Product presentations use every pair of real codes. -/ def prod : Space L M where
  Carrier := P.Carrier × Q.Carrier
  Index := P.Index ⊕ Q.Index
  finiteIndex := inferInstance
  domain := {z | z ∘ Sum.inl ∈ P.domain ∧ z ∘ Sum.inr ∈ Q.domain}
  domain_definable := (P.domain_definable.preimage_comp Sum.inl).inter (Q.domain_definable.preimage_comp Sum.inr)
  decode z := (P.decode ⟨z.val ∘ Sum.inl, z.property.1⟩, Q.decode ⟨z.val ∘ Sum.inr, z.property.2⟩)
  onto := by
    rintro ⟨x, y⟩
    obtain ⟨c, rfl⟩ := P.onto x
    obtain ⟨d, rfl⟩ := Q.onto y
    exact ⟨⟨Sum.elim c.val d.val, c.property, d.property⟩, rfl⟩
  diagonal_definable := by
    have hp := P.diagonal_definable.preimage_comp (Sum.map (Sum.inl : P.Index → P.Index ⊕ Q.Index) (Sum.inl : P.Index → P.Index ⊕ Q.Index))
    have hq := Q.diagonal_definable.preimage_comp (Sum.map (Sum.inr : Q.Index → P.Index ⊕ Q.Index) (Sum.inr : Q.Index → P.Index ⊕ Q.Index))
    convert hp.inter hq using 1
    ext z
    constructor
    · rintro ⟨hx, hy, he⟩
      exact ⟨⟨hx.1, hy.1, congrArg Prod.fst he⟩, ⟨hx.2, hy.2, congrArg Prod.snd he⟩⟩
    · rintro ⟨⟨hx, hy, hp⟩, ⟨hx', hy', hq⟩⟩
      exact ⟨⟨hx, hx'⟩, ⟨hy, hy'⟩, Prod.ext hp hq⟩
end Space
/-- A definable set retains its actual carrier and original parameter base. -/ structure DefSet (P : Space L M) (S : Set M) where
  carrier : Set P.Carrier
  definable : P.Definable S carrier
namespace DefSet
variable {P Q : Space L M} {S : Set M}
instance : CoeSort (DefSet P S) Type := ⟨fun A => A.carrier⟩
def univ (P : Space L M) (S : Set M) : DefSet P S := ⟨Set.univ, P.definable_univ S⟩
end DefSet
end SpecialTransformations.DefinableGeometry
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language
namespace SpecialTransformations.DefinableGeometry
variable {L : Language} {M : Type} [L.Structure M]
namespace Space
variable (P Q R : Space L M)
/-- A finite power retains all codes in every coordinate. -/ def power (ι : Type) [Finite ι] : Space L M where
  Carrier := ι → P.Carrier
  Index := ι × P.Index
  finiteIndex := inferInstance
  domain := {z | ∀ i, (fun j => z (i, j)) ∈ P.domain}
  domain_definable := by
    have h (i : ι) := P.domain_definable.preimage_comp (fun j => (i, j))
    convert Set.definable_iInter_of_finite h using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    rfl
  decode z i := P.decode ⟨fun j => z.val (i, j), z.property i⟩
  onto
    x := by
    choose c hc using fun i => P.onto (x i)
    exact ⟨⟨fun ij => (c ij.1).val ij.2, fun i => (c i).property⟩, funext hc⟩
  diagonal_definable := by
    have h (i : ι) := P.diagonal_definable.preimage_comp (Sum.elim (fun j => Sum.inl (i, j)) (fun j => Sum.inr (i, j)) : P.Index ⊕ P.Index → (ι × P.Index) ⊕ (ι × P.Index))
    have hall := Set.definable_iInter_of_finite h
    convert hall using 1
    ext z
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · rintro ⟨hx, hy, he⟩ i
      exact ⟨hx i, hy i, congrFun he i⟩
    · intro h
      exact ⟨fun i => (h i).choose, fun i => (h i).choose_spec.choose, funext (fun i => (h i).choose_spec.choose_spec)⟩
end Space
end SpecialTransformations.DefinableGeometry
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language
namespace SpecialTransformations
namespace Milestone0
/-- The sorts of `L_RV`, as tags on the single carrier. -/ inductive SortTag where | vf | rv deriving DecidableEq, Repr
/-- Function symbols of `L_RV`, tagged by arity. -/ inductive Fn : ℕ → Type where/-- `0` of the ring language of the `VF` sort -/ | vfZero : Fn 0/-- `1` of the ring language of the `VF` sort -/ | vfOne : Fn 0/-- `+` of the ring language of the `VF` sort -/ | vfAdd : Fn 2/-- `-` of the ring language of the `VF` sort -/ | vfNeg : Fn 1/-- `×` of the ring language of the `VF` sort -/ | vfMul : Fn 2/-- `1` of the group language of the `RV` sort -/ | rvOne : Fn 0/-- the constant `0` of the `RV` sort: the residue field's zero, which is also `rv(0)` and the absorbing element of `RV`. The paper writes this element both as `0` and as `∞`; it is one element, so the language has one constant. -/ | rvZero : Fn 0/-- `×` of the `RV` sort -/ | rvMul : Fn 2/-- Multiplicative inverse on `RV`, totalized by `0⁻¹ = 0`. Naming this symbol is the author-approved correction to the inverse-free language specification before Convention 2.5, required for the intended QE result. It ensures that language substructures contain RV inverses. See LANGUAGE-ERRATA.md. -/ | rvInv : Fn 1/-- `+ : K² → K` of the `RV` sort -/ | kAdd : Fn 2/-- `- : K → K` of the `RV` sort -/ | kNeg : Fn 1/-- the projection `rv : VF → RV` -/ | rvMap : Fn 1
/-- Relation symbols of `L_RV`, tagged by arity. The first two are the sort predicates of the encoding (they are not part of the paper's signature); the last two are the paper's unary predicate `Kˣ` and its preorder `≤`. -/ inductive Rel : ℕ → Type where/-- encoding: the `VF` sort -/ | memVF : Rel 1/-- encoding: the `RV` sort -/ | memRV : Rel 1/-- the paper's unary predicate `Kˣ` -/ | memUnits : Rel 1/-- the paper's preorder `≤` on `RV` -/ | rvLe : Rel 2
/-- The corrected `L_RV`, with named RV inversion, in the tagged one-sorted encoding. -/ def LRV : Language := ⟨Fn, Rel⟩
namespace LRV
/-- Terms of `L_RV` whose (free) variables are indexed by `Fin n`. -/ abbrev Tm (n : ℕ) : Type := LRV.Term (Empty ⊕ Fin n)
/-- Bounded formulas of `L_RV` with `n` variables in scope and no free parameters. -/ abbrev Bf (n : ℕ) : Type := LRV.BoundedFormula Empty n
variable {n : ℕ}
/-- `0` of the `VF` sort -/ def tVFZero : Tm n := Term.func Fn.vfZero fun i => i.elim0
/-- `1` of the `VF` sort -/ def tVFOne : Tm n := Term.func Fn.vfOne fun i => i.elim0
/-- `+` of the `VF` sort -/ def tVFAdd (t u : Tm n) : Tm n := Term.func Fn.vfAdd ![t, u]
/-- `-` of the `VF` sort -/ def tVFNeg (t : Tm n) : Tm n := Term.func Fn.vfNeg ![t]
/-- `×` of the `VF` sort -/ def tVFMul (t u : Tm n) : Tm n := Term.func Fn.vfMul ![t, u]
/-- `1` of the `RV` sort -/ def tRVOne : Tm n := Term.func Fn.rvOne fun i => i.elim0
/-- `0` of the `RV` sort -/ def tRVZero : Tm n := Term.func Fn.rvZero fun i => i.elim0
/-- The paper's `∞` is `rv(0)`, i.e. the absorbing element `rvZero` of the `RV` sort: the paper's two symbols `0` and `∞` name one element. Kept as a definition so that the axioms can be read in the paper's notation. -/ def tRVInfty : Tm n := tRVZero
/-- `×` of the `RV` sort -/ def tRVMul (t u : Tm n) : Tm n := Term.func Fn.rvMul ![t, u]
/-- Multiplicative inverse on the `RV` sort, with `0⁻¹ = 0`. -/ def tRVInv (t : Tm n) : Tm n := Term.func Fn.rvInv ![t]
/-- `+ : K² → K` of the `RV` sort -/ def tKAdd (t u : Tm n) : Tm n := Term.func Fn.kAdd ![t, u]
/-- `- : K → K` of the `RV` sort -/ def tKNeg (t : Tm n) : Tm n := Term.func Fn.kNeg ![t]
/-- the projection `rv : VF → RV` -/ def tRv (t : Tm n) : Tm n := Term.func Fn.rvMap ![t]
/-- the bound variable of index `i < n` -/ def tv (i : ℕ) (h : i < n) : Tm n := Term.var (Sum.inr ⟨i, h⟩)
/-- the numeral `k · 1` of the `VF` sort -/ def tVFNumeral : ℕ → Tm n | 0 => tVFZero | k + 1 => tVFAdd (tVFNumeral k) tVFOne
/-- `t ^ k`, in the `RV` sort -/ def tRVPow (t : Tm n) : ℕ → Tm n | 0 => tRVOne | k + 1 => tRVMul (tRVPow t k) t
/-- `t ∈ VF`, the encoding's sort predicate for the `VF` sort -/ def pVF (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memVF t
/-- `t ∈ RV`, the encoding's sort predicate for the `RV` sort -/ def pRVsort (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memRV t
/-- the paper's unary predicate `Kˣ` -/ def pUnits (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memUnits t
/-- the paper's preorder `≤` -/ def pLe (t u : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₂ Rel.rvLe t u
/-- `t = u` -/ def pEq (t u : Tm n) : Bf n := t =' u
/-- the paper's `RV = RV-sort ∖ {0}` -/ def pRV (t : Tm n) : Bf n := ∼(pEq t tRVZero)
/-- the strict order `t > 1` of the `RV` sort -/ def pGtOne (t : Tm n) : Bf n := pLe tRVOne t ⊓ ∼(pLe t tRVOne)
/-- `t ∈ K = K^× ∪ {0}`, the residue field inside the `RV` sort. Not the same as `t ≠ 0`: when `Γ` is nontrivial the elements of `RV ∖ {0}` of value `≠ 1` are not in `K`, and the residue-field operations are junk there. Definition 2.1(d) defines `K` as `K^× ∪ {0}`, with `K^×` the predicate, i.e. axiom (4)'s class of `1`. The `0` here is `rv(0)`, the absorbing element of `RV`. -/ def pInK (t : Tm n) : Bf n := pUnits t ⊔ pEq t tRVZero
end LRV
namespace LRV
/-- the sort predicate of the sort `s`, as a formula -/ def sortPred (s : SortTag) (t : Tm n) : Bf n := match s with | .vf => pVF t | .rv => pRVsort t
/-- `⋀ i, x_i ∈ s_i`, for the variables `x_i` of index `i` -/ def sortedHyps {k : ℕ} (ss : Fin k → SortTag) : Bf k := (List.finRange k).foldr (fun i acc => sortPred (ss i) (tv i.val i.isLt) ⊓ acc) ⊤
/-- the guarded universal sentence `∀ x̄, (⋀ i, x_i ∈ s_i) → φ` -/ def allSorted {k : ℕ} (ss : Fin k → SortTag) (φ : Bf k) : LRV.Sentence := BoundedFormula.alls (sortedHyps ss ⟹ φ)
/-- the guarded existential formula `∃ x ∈ s, φ`, where `x` is the variable of index `k` -/ def exSorted {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) : Bf k := BoundedFormula.ex (sortPred s (tv k (Nat.lt_succ_self k)) ⊓ φ)
/-- `⋀ i < k, x_i ∈ K`: the tuple lies in `K = K^× ∪ {0}` -/ def kHyps {k : ℕ} : Bf k := (List.finRange k).foldr (fun i acc => pInK (tv i.val i.isLt) ⊓ acc) ⊤
/-- the universal sentence `∀ x̄ ∈ s̄ ∩ K, φ` -/ def allSortedK {k : ℕ} (ss : Fin k → SortTag) (φ : Bf k) : LRV.Sentence := BoundedFormula.alls ((sortedHyps ss ⊓ kHyps) ⟹ φ)
/-- the guarded existential formula `∃ x ∈ s ∩ K, φ`, with `x` the variable of index `k` -/ def exSortedK {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) : Bf k := BoundedFormula.ex (sortPred s (tv k (Nat.lt_succ_self k)) ⊓ pInK (tv k (Nat.lt_succ_self k)) ⊓ φ)
/-- the universal closure of a formula in a single variable -/ def allOne (φ : Bf 1) : LRV.Sentence := BoundedFormula.alls φ
/-- The result sort of a function symbol of `L_RV`. -/ def Fn.resSort : {l : ℕ} → Fn l → SortTag | _, .vfZero => .vf | _, .vfOne => .vf | _, .vfAdd => .vf | _, .vfNeg => .vf | _, .vfMul => .vf | _, .rvOne => .rv | _, .rvZero => .rv | _, .rvMul => .rv | _, .rvInv => .rv | _, .kAdd => .rv | _, .kNeg => .rv | _, .rvMap => .rv
/-- The sort of the `i`-th argument of a function symbol of `L_RV`. -/ def Fn.argSort : {l : ℕ} → (f : Fn l) → Fin l → SortTag | _, .vfZero => Fin.elim0 | _, .vfOne => Fin.elim0 | _, .vfAdd => fun _ => .vf | _, .vfNeg => fun _ => .vf | _, .vfMul => fun _ => .vf | _, .rvOne => Fin.elim0 | _, .rvZero => Fin.elim0 | _, .rvMul => fun _ => .rv | _, .rvInv => fun _ => .rv | _, .kAdd => fun _ => .rv | _, .kNeg => fun _ => .rv | _, .rvMap => fun _ => .vf
/-- Horner form `x^k + a_{k-1} x^{k-1} + ⋯ + a_0` of the monic polynomial of degree `k` whose coefficients are the variables `0, …, k-1` and whose variable is the variable `k`. The leading term is `x ^ k`, so `acfScheme` quantifies over *all* monic polynomials of degree `k`. (An earlier version started the Horner fold at `x` instead of at `x + a_{k-1}`, which silently produced `x^{k+1} + a_{k-1}x^{k-1} + ⋯ + a_0` — a monic polynomial of degree `k+1` with zero `x^k` coefficient, so the scheme covered only a proper subclass and did not give algebraic closedness.) For `k = 0` the value is immaterial: `acfScheme` is only used with `1 ≤ k`. -/ def hornerPoly {k : ℕ} (add mul : {n : ℕ} → Tm n → Tm n → Tm n) : Tm (k + 1) := match k with
  | 0 => tv 0 Nat.zero_lt_one
  | (n + 1) =>
    let x : Tm (n + 1 + 1) := tv (n + 1) (by omega)
    (List.finRange n).reverse.foldl (fun acc i => add (mul acc x) (tv i.val (by omega))) (add x (tv n (by omega)))
end LRV
namespace Axioms
open LRV
/-- The sentences of a finite list, as a theory. -/ def ofList (l : List LRV.Sentence) : LRV.Theory := {s | s ∈ l}
/-- the carrier is covered by the two sorts -/ def sdCover : LRV.Sentence := allOne (pVF &0 ⊔ pRVsort &0)
/-- the two sorts are disjoint -/ def sdDisjoint : LRV.Sentence := allOne (∼(pVF &0 ⊓ pRVsort &0))
/-- `0` of the ring language lies in the `VF` sort -/ def sdVFZero : LRV.Sentence := pVF tVFZero
/-- `1` of the ring language lies in the `VF` sort -/ def sdVFOne : LRV.Sentence := pVF tVFOne
/-- the `VF` sort is closed under `+` -/ def sdVFAdd : LRV.Sentence := allSorted ![.vf, .vf] (pVF (tVFAdd &0 &1))
/-- the `VF` sort is closed under `-` -/ def sdVFNeg : LRV.Sentence := allSorted ![.vf] (pVF (tVFNeg &0))
/-- the `VF` sort is closed under `×` -/ def sdVFMul : LRV.Sentence := allSorted ![.vf, .vf] (pVF (tVFMul &0 &1))
/-- `rv` maps the `VF` sort into the `RV` sort -/ def sdRv : LRV.Sentence := allSorted ![.vf] (pRVsort (tRv &0))
/-- `0` of the `RV` sort lies in the `RV` sort -/ def sdRVZero : LRV.Sentence := pRVsort tRVZero
/-- `∞` lies in the `RV` sort -/ def sdRVInfty : LRV.Sentence := pRVsort tRVInfty
/-- `1` of the `RV` sort lies in the `RV` sort -/ def sdRVOne : LRV.Sentence := pRVsort tRVOne
/-- the `RV` sort is closed under `×` -/ def sdRVMul : LRV.Sentence := allSorted ![.rv, .rv] (pRVsort (tRVMul &0 &1))
def sdRVInv : LRV.Sentence := allSorted ![.rv] (pRVsort (tRVInv &0))
/-- The predicate `Kˣ` holds only of elements of the `RV` sort. Its actual content is axiom (4)'s `leClassOne`, which makes `Kˣ` the class of `1` — a *proper* subgroup of the multiplicative group `RV ∖ {0}` whenever `Γ` is nontrivial. Identifying `Kˣ` with all of `RV ∖ {0}` puts every `x ≠ 0` in the class of `1`, hence `1 ≤ x ≤ 1`, hence makes the preorder trivial and `Γ` trivial — contradicting the paper's standing hypothesis that `Γ(S)` is nontrivial. -/ def sdUnits : LRV.Sentence := allOne (pUnits &0 ⟹ pRVsort &0)
/-- `K = Kˣ ∪ {0}` is closed under `+` -/ def sdKAdd : LRV.Sentence := allSorted ![.rv, .rv] (pInK &0 ⟹ (pInK &1 ⟹ pInK (tKAdd &0 &1)))
/-- `K` is closed under unary `-` -/ def sdKNeg : LRV.Sentence := allSorted ![.rv] (pInK &0 ⟹ pInK (tKNeg &0))
/-- `K` is closed under `×`: the paper's `K = K^× ∪ {0}` is a field, so the product of two elements of `K` is in `K` and not `∞`. Without this the field axioms of `kField` (which are guarded by `pK`) constrain only the products that happen to land in `K`. -/ def sdKMul : LRV.Sentence := allSorted ![.rv, .rv] (pInK &0 ⟹ (pInK &1 ⟹ pInK (tRVMul &0 &1)))
/-- The closure part of the sort discipline: each sort is closed under its own symbols, and the two sorts are related through the symbols that cross them. -/ def sortClosure : LRV.Theory := ofList [sdVFZero, sdVFOne, sdVFAdd, sdVFNeg, sdVFMul, sdRv, sdRVZero, sdRVInfty, sdRVOne, sdRVMul, sdRVInv, sdUnits, sdKAdd, sdKNeg, sdKMul]
/-- the sort discipline of the encoding, as a theory -/ def sortAxioms : LRV.Theory := sortClosure ∪ ofList [sdCover, sdDisjoint]
/-- the field axioms for the sort `s`, with that sort's `0`, `1`, `+`, `-`, `×` -/ def fieldAxioms (s : SortTag) (zero one : {n : ℕ} → Tm n) (add mul : {n : ℕ} → Tm n → Tm n → Tm n) (neg : {n : ℕ} → Tm n → Tm n) : List LRV.Sentence := [ /- associativity of `+` -/ allSorted ![s, s, s] (pEq (add (add &0 &1) &2) (add &0 (add &1 &2))), /- commutativity of `+` -/ allSorted ![s, s] (pEq (add &0 &1) (add &1 &0)), /- `0` is neutral for `+` -/ allSorted ![s] (pEq (add &0 zero) &0), /- additive inverses -/ allSorted ![s] (pEq (add &0 (neg &0)) zero), /- associativity of `×` -/ allSorted ![s, s, s] (pEq (mul (mul &0 &1) &2) (mul &0 (mul &1 &2))), /- commutativity of `×` -/ allSorted ![s, s] (pEq (mul &0 &1) (mul &1 &0)), /- `1` is neutral for `×` -/ allSorted ![s] (pEq (mul &0 one) &0), /- distributivity -/ allSorted ![s, s, s] (pEq (mul &0 (add &1 &2)) (add (mul &0 &1) (mul &0 &2))), /- `0 ≠ 1` -/ ∼(pEq zero one), /- every nonzero element is invertible: the language has no inverse symbol -/ allSorted ![s] (pEq &0 zero ⊔ exSorted s (pEq (mul &0 &1) one)) ]
/-- the algebraic-closedness scheme for the sort `s`: `∀ a₀ … a_{k-1} ∃ x, x^k + a_{k-1} x^{k-1} + ⋯ + a₀ = 0` -/ def acfScheme (s : SortTag) (zero : {n : ℕ} → Tm n) (add mul : {n : ℕ} → Tm n → Tm n → Tm n) (k : ℕ) : LRV.Sentence := allSorted (fun _ : Fin k => s) (exSorted s (pEq (hornerPoly add mul) zero))
/-- Definition 2.2 item 1: `(VF, 0, 1, +, -, ×)` is an algebraically closed field. -/ def vfField : LRV.Theory := ofList (fieldAxioms .vf tVFZero tVFOne tVFAdd tVFMul tVFNeg)
/-- algebraic closedness of the `VF` sort -/ def vfAlgClosed : LRV.Theory := {s | ∃ k, 1 ≤ k ∧ s = acfScheme .vf tVFZero tVFAdd tVFMul k}
/-- Definition 2.2 item 3: `(K, 0, 1, +, -, ×)` is an algebraically closed field, where `K = K^× ∪ {0}`, the units of `RV` together with the absorbing element `0 = ∞ = rv 0`. Every quantifier is relativised to `K` (`allSortedK`, `exSortedK`), not merely to the `RV` sort. This is not cosmetic: `RV^×` also contains the elements of value `≠ 1`, where the residue operations are junk, so asserting the field axioms at every element of `RV` (equivalently at every `t ≠ ∞`, since `RV ∖ {0}` *is* the group) would force `Γ` trivial. -/ def kField : LRV.Theory := ofList [ /- associativity of `+` -/ allSortedK ![.rv, .rv, .rv] (pEq (tKAdd (tKAdd &0 &1) &2) (tKAdd &0 (tKAdd &1 &2))), /- commutativity of `+` -/ allSortedK ![.rv, .rv] (pEq (tKAdd &0 &1) (tKAdd &1 &0)), /- `0` is neutral for `+` -/ allSortedK ![.rv] (pEq (tKAdd &0 tRVZero) &0), /- additive inverses -/ allSortedK ![.rv] (pEq (tKAdd &0 (tKNeg &0)) tRVZero), /- associativity of `×` -/ allSortedK ![.rv, .rv, .rv] (pEq (tRVMul (tRVMul &0 &1) &2) (tRVMul &0 (tRVMul &1 &2))), /- commutativity of `×` -/ allSortedK ![.rv, .rv] (pEq (tRVMul &0 &1) (tRVMul &1 &0)), /- `1` is neutral for `×` -/ allSortedK ![.rv] (pEq (tRVMul &0 tRVOne) &0), /- distributivity -/ allSortedK ![.rv, .rv, .rv] (pEq (tRVMul &0 (tKAdd &1 &2)) (tKAdd (tRVMul &0 &1) (tRVMul &0 &2))), /- `0 ≠ 1` -/ ∼(pEq tRVZero tRVOne), /- every nonzero element of `K` is invertible -/ allSortedK ![.rv] (pEq &0 tRVZero ⊔ exSortedK .rv (pEq (tRVMul &0 &1) tRVOne)) ]
/-- the algebraic-closedness scheme for `K = K^× ∪ {0}`: coefficients and root in `K` -/ def acfSchemeK (k : ℕ) : LRV.Sentence := allSortedK (fun _ : Fin k => .rv) (exSortedK .rv (pEq (hornerPoly tKAdd tRVMul) tRVZero))
/-- algebraic closedness of `K = K^× ∪ {0}` -/ def kAlgClosed : LRV.Theory := {s | ∃ k, 1 ≤ k ∧ s = acfSchemeK k}
/-- `1 ∈ Kˣ` -/ def rvOneMem : LRV.Sentence := pUnits tRVOne
/-- `Kˣ` is closed under `×` -/ def rvMulMem : LRV.Sentence := allSorted ![.rv, .rv] (pUnits &0 ⟹ (pUnits &1 ⟹ pUnits (tRVMul &0 &1)))
/-- `×` is associative on `RV` -/ def rvMulAssoc : LRV.Sentence := allSorted ![.rv, .rv, .rv] (pEq (tRVMul (tRVMul &0 &1) &2) (tRVMul &0 (tRVMul &1 &2)))
/-- `×` is commutative on `RV` -/ def rvMulComm : LRV.Sentence := allSorted ![.rv, .rv] (pEq (tRVMul &0 &1) (tRVMul &1 &0))
/-- `1` is neutral for `×` on `Kˣ` -/ def rvMulOne : LRV.Sentence := allSorted ![.rv] (pUnits &0 ⟹ pEq (tRVMul tRVOne &0) &0)
/-- every element of `Kˣ` is invertible in `Kˣ` -/ def rvMulInv : LRV.Sentence := allSorted ![.rv] (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVMul &1 &0) tRVOne))
/-- divisibility of `Kˣ`: for every `k ≥ 1`, `∀ x ∈ Kˣ ∃ y ∈ Kˣ, y^k = x` -/ def rvDivisible (k : ℕ) : LRV.Sentence := allSorted ![.rv] (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVPow &1 k) &0))
/-- `t × 0 = 0` for `t ∈ K` -/ def rvMulZeroK : LRV.Sentence := allSorted ![.rv] (pInK &0 ⟹ pEq (tRVMul &0 tRVZero) tRVZero)
/-- `t × 0 = 0` for every `t` of the `RV` sort: the absorbing element. (This is the paper's `t × ∞ = ∞`; `∞ = rv 0 = 0`.) -/ def rvMulInfty : LRV.Sentence := allSorted ![.rv] (pEq (tRVMul &0 tRVInfty) tRVInfty)
/-- Definition 2.2 item 2: `(RV^×, 1, ×)` is a divisible abelian group, with `×` augmented by `t × 0 = 0`, i.e. `0 = ∞ = rv 0` absorbing. -/ def rvGroup : LRV.Theory := ofList [rvOneMem, rvMulMem, rvMulAssoc, rvMulComm, rvMulOne, rvMulInv, rvMulZeroK, rvMulInfty] ∪ {s | ∃ k, 1 ≤ k ∧ s = rvDivisible k}
/-- `≤` is reflexive on `RV` -/ def leRefl : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pLe &0 &0)
/-- `≤` is transitive on `RV` -/ def leTrans : LRV.Sentence := allSorted ![.rv, .rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pLe &0 &1 ⟹ (pLe &1 &2 ⟹ pLe &0 &2)))))
/-- `≤` is total on `RV` -/ def leTotal : LRV.Sentence := allSorted ![.rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pLe &0 &1 ⊔ pLe &1 &0)))
/-- `∞` is the top element of `RV` -/ def leTop : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pLe &0 tRVInfty)
/-- `∞ ≤ x` forces `x = ∞`, i.e. `∞` is alone in its class -/ def leInftyEq : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ (pLe tRVInfty &0 ⟹ pEq &0 tRVInfty))
/-- `Kˣ` is the equivalence class of `1` -/ def leClassOne : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ (pUnits &0 ⇔ (pLe tRVOne &0 ⊓ pLe &0 tRVOne)))
/-- `≤` is compatible with `×` on the left, i.e. the induced order on `RV/Kˣ` is a translation-invariant order -/ def leMulCompat : LRV.Sentence := allSorted ![.rv, .rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pUnits &2 ⟹ (pLe &0 &1 ⟹ pLe (tRVMul &0 &2) (tRVMul &1 &2))))))
/-- Definition 2.2 item 4: `≤` is a preorder on `RV` with `∞` the top element and `Kˣ` the equivalence class of `1`. -/ def preorderRV : LRV.Theory := ofList [leRefl, leTrans, leTotal, leTop, leInftyEq, leClassOne, leMulCompat]
/-- `rv(0) = ∞` -/ def rvZeroEq : LRV.Sentence := pEq (tRv tVFZero) tRVInfty
/-- `rv(x) = ∞` forces `x = 0` -/ def rvEqInfty : LRV.Sentence := allSorted ![.vf] (pEq (tRv &0) tRVInfty ⟹ pEq &0 tVFZero)
/-- `rv` is a group homomorphism on `VF^×` -/ def rvMulHom : LRV.Sentence := allSorted ![.vf, .vf] (pEq (tRv (tVFMul &0 &1)) (tRVMul (tRv &0) (tRv &1)))
/-- **`rv` is surjective**: every element of the `RV` sort other than `rv(0)` is `rv(x)` for some `x ∈ VF`. (Definition 2.2(6): `rv : VF^× → RV^×` is surjective, augmented by `rv(0) = ∞ = 0`. With `RV^× = RV ∖ {0}` this says: `RV = rv(VF^×) ∪ {0}`, so there are no `RV`-elements outside the image of `rv`.) -/ def rvSurj : LRV.Sentence := allSorted ![.rv] (∼(pEq &0 tRVZero) ⟹ exSorted .vf (pEq (tRv &1) &0))
/-- the ultrametric inequality for `vv = vrv ∘ rv`: `vv(x+y) ≥ min(vv x, vv y)` -/ def rvUltrametric : LRV.Sentence := allSorted ![.vf, .vf] (pLe (tRv &0) (tRv (tVFAdd &0 &1)) ⊔ pLe (tRv &1) (tRv (tVFAdd &0 &1)))
/-- Definition 2.2 item 6: `rv : VF^× → RV^×` is a surjective group homomorphism augmented by `rv(0) = ∞`, and `vv = vrv ∘ rv` is a valuation. (The valuation ring `O = rv⁻¹(RV^{≥1})` and the maximal ideal `M = rv⁻¹(RV^{>1})` are *defined* from `rv`, so — exactly as in the paper — they need no symbols of their own.) -/ def rvAxioms : LRV.Theory := ofList [rvZeroEq, rvEqInfty, rvMulHom, rvSurj, rvUltrametric]
/-- `1` is neutral for `×` on every nonzero `RV`-element. -/ def rvMulOneRV : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pEq (tRVMul tRVOne &0) &0)
/-- every nonzero `RV`-element is invertible in `RV^×`. -/ def rvMulInvRV : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ exSorted .rv (pRV &1 ⊓ pEq (tRVMul &1 &0) tRVOne))
/-- the order on `RV` is invariant under scaling by any `c ≠ rv 0`, in both directions. The guards on the first two variables are dropped because `∞ = rv 0` is absorbing and top, so both sides hold there. -/ def leMulCompatFull : LRV.Sentence := allSorted ![.rv, .rv, .rv] (pRV &2 ⟹ (pLe &0 &1 ⇔ pLe (tRVMul &0 &2) (tRVMul &1 &2)))
/-- `kAdd` is the residue addition at units: `rv (x + y)` if that is a unit, and `0` if `x + y` drops into the maximal ideal. -/ def kAddLink : LRV.Sentence := allSorted ![.vf, .vf] (pUnits (tRv &0) ⟹ (pUnits (tRv &1) ⟹ ((pUnits (tRv (tVFAdd &0 &1)) ⟹ pEq (tKAdd (tRv &0) (tRv &1)) (tRv (tVFAdd &0 &1))) ⊓ (∼(pUnits (tRv (tVFAdd &0 &1))) ⟹ pEq (tKAdd (tRv &0) (tRv &1)) tRVZero))))
/-- `kNeg` is the residue negation at units. -/ def kNegLink : LRV.Sentence := allSorted ![.vf] (pUnits (tRv &0) ⟹ pEq (tKNeg (tRv &0)) (tRv (tVFNeg &0)))
/-- two elements of `VF` have the same residue iff their difference has strictly larger value than the second: `rv a = rv b ↔ ¬ (v (a - b) ≤ v b)`. (The first transcription had the two `pLe` arguments transposed, which made the axiom false at `a = b = 1` and the whole theory inconsistent — see `QE-PLAN.md` and `.ultramath/smw163dd5/m5/Audit.lean`.) -/ def rvEqLink : LRV.Sentence := allSorted ![.vf, .vf] (∼(pEq &1 tVFZero) ⟹ (pEq (tRv &0) (tRv &1) ⇔ ∼(pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &1))))
/-- the junk convention for `kAdd` off `K`: the value is `0`. -/ def kJunkZero : LRV.Sentence := allSorted ![.rv, .rv] ((∼(pInK &0) ⊔ ∼(pInK &1)) ⟹ pEq (tKAdd &0 &1) tRVZero)
/-- the junk convention for `kNeg` off `K`. -/ def kNegJunkZero : LRV.Sentence := allSorted ![.rv] (∼(pInK &0) ⟹ pEq (tKNeg &0) tRVZero)
/-- **Nontriviality**: some nonzero element of `VF` has value strictly below the value of `1`, i.e. lies in the maximal ideal. -/ def axNontrivialRV : LRV.Sentence := exSorted .vf (∼(pEq &0 tVFZero) ⊓ ∼(pLe (tRv &0) (tRv tVFOne)))
/-- The inverse operation fixes the absorbing element `0 = ∞`. -/ def rvInvZero : LRV.Sentence := pEq (tRVInv tRVZero) tRVZero
/-- The named inverse is a multiplicative inverse on the nonzero `RV` group. -/ def rvInvMul : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pEq (tRVMul (tRVInv &0) &0) tRVOne)
/-- The added axioms, in one theory. -/ def repairRV : LRV.Theory := ofList [rvMulOneRV, rvMulInvRV, leMulCompatFull, kAddLink, kNegLink, rvEqLink, kJunkZero, kNegJunkZero, axNontrivialRV, rvInvZero, rvInvMul]
/-- the paper's own content of `ACVF`: Definition 2.2, items 1–6 -/ def ACVFpaper : LRV.Theory := vfField ∪ vfAlgClosed ∪ rvGroup ∪ kField ∪ kAlgClosed ∪ preorderRV ∪ rvAxioms ∪ repairRV ∪ repairRV
/-- **The theory `ACVF` of Definition 2.2**, in the tagged encoding: items 1–6 plus the sort discipline of the encoding. -/ def ACVF : LRV.Theory := sortAxioms ∪ ACVFpaper
/-- characteristic zero of the `VF` sort -/ def charZeroVF (k : ℕ) : LRV.Sentence := ∼(pEq (tVFNumeral (k + 1)) tVFZero)
/-- residue characteristic zero: for each prime `p`, `p · 1` is a unit of the valuation ring, i.e. `¬ (1 < rv(p·1))` -/ def residueCharZero (p : ℕ) : LRV.Sentence := ∼(pGtOne (tRv (tVFNumeral p)))
/-- **The theory `ACVF(0,0)`**: `ACVF` with pure characteristic `0`, i.e. characteristic `0` for the valued field and characteristic `0` for its residue field. -/ def ACVF00 : LRV.Theory := ACVF ∪ {s | ∃ k, s = charZeroVF k} ∪ {s | ∃ p, p.Prime ∧ s = residueCharZero p}
end Axioms
open Axioms LRV
/-- Whether an element of a model has a given sort. -/ def sortEval {M : Type*} [LRV.Structure M] : SortTag → M → Prop | .vf => fun x => Structure.RelMap (L := LRV) Rel.memVF ![x] | .rv => fun x => Structure.RelMap (L := LRV) Rel.memRV ![x]
variable {M : Type*} [LRV.Structure M]
/-- `x` lies in the `VF` sort -/ def iVF (x : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memVF ![x]
/-- `x` lies in the `RV` sort -/ def iRV (x : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memRV ![x]
/-- the preorder `≤` of the `RV` sort -/ def iLe (x y : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.rvLe ![x, y]
/-- the interpretation of `+` of the `VF` sort -/ def iVFAdd (x y : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfAdd ![x, y]
/-- the interpretation of `×` of the `VF` sort -/ def iVFMul (x y : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfMul ![x, y]
/-- the interpretation of the projection `rv : VF → RV` -/ def iRv (x : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvMap ![x]
/-- the interpretation of `0` of the `RV` sort -/ def iRVZero : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvZero fun i => i.elim0
end Milestone0
end SpecialTransformations
end
section
reset_statement_module_caches set_option autoImplicit true
open Classical FirstOrder FirstOrder.Language FirstOrder SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Milestone0.Transfer
/-- `0` of the `VF` sort -/ def iVFZero {M : Type} [LRV.Structure M] : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfZero fun i => i.elim0
/-- `1` of the `VF` sort -/ def iVFOne {M : Type} [LRV.Structure M] : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfOne fun i => i.elim0
end SpecialTransformations.Milestone0.Transfer
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV FirstOrder FirstOrder.Language FirstOrder SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV FirstOrder FirstOrder.Language FirstOrder SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Milestone0.Transfer
variable {M : Type} [LRV.Structure M]
theorem rv_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iRV (iRv x) := by sorry
theorem rv_zero_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iRV (iRVZero (M := M))  := by sorry
end SpecialTransformations.Milestone0.Transfer
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0
namespace SpecialTransformations.Milestone0
namespace RVCalc
variable {M : Type} [LRV.Structure M]
open LRV SpecialTransformations.Milestone0.Transfer
/-- `≤` is reflexive at every `RV`-element (`leRefl` is guarded by `≠ 0`; at `0` the statement is the ultrametric axiom at `(0,0)` together with `rv 0 = 0`). -/ theorem le_refl_rv (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) : iLe a a := by sorry
theorem le_trans_rv (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
    (hab : iLe a b) (hbc : iLe b c) : iLe a c := by sorry
end RVCalc
end SpecialTransformations.Milestone0
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Milestone0
namespace Transfer
section VFField
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- The `VF` sort of an `ACVF`-model, as a type. -/ def VFType : Type := { x : M // iVF x }
noncomputable def vfFieldOfModel {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] : Field (VFType (M := M)) := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `SpecialTransformations.Milestone0.Transfer.vfFieldOfModel 28)
end VFField
end Transfer
end SpecialTransformations.Milestone0
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Milestone0.VFValued
section Model
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- The `Field` structure on the `VF` sort, as an instance, so that `IsValPred`'s `CommRing` requirement is discharged by typeclass search. -/ noncomputable instance instFieldVFType : Field (Transfer.VFType (M := M)) := Transfer.vfFieldOfModel (M := M) (hM := hM)
/-- The paper's `v x ≤ v y` on the `VF` sort: `iLe (rv y) (rv x)`. -/ def predV (x y : Transfer.VFType (M := M)) : Prop := iLe (iRv y.1) (iRv x.1)
/-- **Every model of the frozen `ACVF` carries a genuine Mathlib valuation on its `VF` sort**, and `predV` is that valuation's order: `iLe (rv y) (rv x) ↔ w x ≤ w y`. -/ theorem exists_valuation_predV : ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ) (w : Valuation (Transfer.VFType (M := M)) Γ), ∀ x y : Transfer.VFType (M := M), predV x y ↔ w x ≤ w y := by sorry
end Model
end SpecialTransformations.Milestone0.VFValued
end
section
reset_statement_module_caches set_option autoImplicit true
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace CanonicalStructure
variable {M : Type} [sM : LRV.Structure M]
def sortZero (s : SortTag) : M := match s with
  | .vf => Transfer.iVFZero
  | .rv => iRVZero
/-- Correctly sorted applications retain their original interpretation. Wrong-sort applications return the named zero of the result sort. -/ @[instance_reducible]
noncomputable def normalize : LRV.Structure M where
  funMap f xs := if ∀ i, sortEval (Fn.argSort f i) (xs i) then Structure.funMap (L := LRV) f xs else sortZero (Fn.resSort f)
  RelMap r
    xs :=   match r with
    | .memVF => Structure.RelMap (L := LRV) Rel.memVF xs
    | .memRV => Structure.RelMap (L := LRV) Rel.memRV xs
    | .memUnits => Structure.RelMap (L := LRV) Rel.memUnits xs
    | .rvLe => (∀ i, sortEval .rv (xs i)) ∧ Structure.RelMap (L := LRV) Rel.rvLe xs
/-- The off-sort choices used by the canonical totalization. The three unary predicates retain the constraints already imposed by the sort axioms. -/ def IsCanonical : Prop := (∀ {k : ℕ} (f : Fn k) (xs : Fin k → M), ¬(∀ i, sortEval (Fn.argSort f i) (xs i)) → Structure.funMap (L := LRV) f xs = sortZero (Fn.resSort f)) ∧ (∀ xs : Fin 2 → M, ¬(∀ i, sortEval .rv (xs i)) → ¬Structure.RelMap (L := LRV) Rel.rvLe xs)
end CanonicalStructure
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
namespace CanonicalRV
noncomputable def equivOfSameFibers {A B C : Type*} (f : A → B) (g : A → C) (hf : Function.Surjective f) (hg : Function.Surjective g) (h : ∀ a b, f a = f b ↔ g a = g b) : B ≃ C where
  toFun b := g (Classical.choose (hf b))
  invFun c := f (Classical.choose (hg c))
  left_inv
    b := by
    have he := Classical.choose_spec (hg (g (Classical.choose (hf b))))
    exact ((h _ _).mpr he).trans (Classical.choose_spec (hf b))
  right_inv
    c := by
    have he := Classical.choose_spec (hf (f (Classical.choose (hg c))))
    exact ((h _ _).mp he).trans (Classical.choose_spec (hg c))
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
abbrev RVSort (M : Type) [LRV.Structure M] := { x : M // iRV x }
def encodedRv (a : VFType (M := M)) : RVSort M := ⟨iRv a.1, rv_mem hM a.2⟩
theorem encodedRv_surjective : Function.Surjective (encodedRv (M := M)) := by sorry
end CanonicalRV
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M]
def FinitelySatisfiable {α : Type} {n : ℕ} (v : α → M) (p : Set (LRV.BoundedFormula α n)) : Prop := ∀ l : List (LRV.BoundedFormula α n), (∀ φ ∈ l, φ ∈ p) → ∃ x : Fin n → M, ∀ φ ∈ l, φ.Realize v x
def Saturated (M : Type) [LRV.Structure M] (κ : Cardinal) : Prop := ∀ (α : Type) (v : α → M), Cardinal.mk α < κ → ∀ {n : ℕ} (p : Set (LRV.BoundedFormula α n)), FinitelySatisfiable v p → ∃ x : Fin n → M, ∀ φ ∈ p, φ.Realize v x
def PartialElementary {α : Type} (v w : α → M) : Prop := ∀ {n : ℕ} (φ : LRV.BoundedFormula α n) (a : Fin n → α), φ.Realize v (v ∘ a) ↔ φ.Realize w (w ∘ a)
def StronglyHomogeneous (M : Type) [LRV.Structure M] (κ : Cardinal) : Prop := ∀ (α : Type) (v w : α → M), Cardinal.mk α < κ → PartialElementary v w → ∃ e : M ≃[LRV] M, ∀ a, e (v a) = w a
end SpecialTransformations.Section3
end
section
reset_statement_module_caches set_option autoImplicit true
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
namespace SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M]
def vfValues {n : ℕ} (x : Fin n → VFType (M := M)) : Fin n → M := fun i => (x i).val
def rvValues {n : ℕ} (x : Fin n → CanonicalRV.RVSort M) : Fin n → M := fun i => (x i).val
noncomputable def rawVFSpace (n : ℕ) : DefinableGeometry.Space LRV M where
  Carrier := Fin n → VFType (M := M)
  Index := Fin n
  finiteIndex := inferInstance
  domain := Set.range (vfValues (n := n))
  domain_definable := by sorry
  decode z := Classical.choose z.property
  onto := by sorry
  diagonal_definable := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `SpecialTransformations.Section4.rawVFSpace 19)
noncomputable def rawRVSpace (n : ℕ) : DefinableGeometry.Space LRV M where
  Carrier := Fin n → CanonicalRV.RVSort M
  Index := Fin n
  finiteIndex := inferInstance
  domain := Set.range (rvValues (n := n))
  domain_definable := by sorry
  decode z := Classical.choose z.property
  onto := by sorry
  diagonal_definable := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `SpecialTransformations.Section4.rawRVSpace 18)
noncomputable def rawMixedSpace (n r : ℕ) : DefinableGeometry.Space LRV M := (rawVFSpace n).prod (rawRVSpace r)
end SpecialTransformations.Section4
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- The standing convention after Definition 2.4 that the VF part of S is a field, stated separately from the genuine saturation assumptions. -/ structure VFFieldBase (S : Set M) where
  field : Subfield (VFType (M := M))
  mem_iff : ∀ x : VFType (M := M), x ∈ field ↔ x.val ∈ S
end SpecialTransformations.Section3
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Values
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- Equality of values, rather than equality of RV classes. -/ def sameValue (x y : CanonicalRV.RVSort M) : Prop := iLe x.val y.val ∧ iLe y.val x.val
def valueSetoid : Setoid (CanonicalRV.RVSort M) where
  r := sameValue
  iseqv := ⟨fun x => ⟨RVCalc.le_refl_rv hM x.property, RVCalc.le_refl_rv hM x.property⟩, fun h => ⟨h.2, h.1⟩, fun {x y z} hxy hyz => ⟨RVCalc.le_trans_rv hM x.property y.property z.property hxy.1 hyz.1, RVCalc.le_trans_rv hM z.property y.property x.property hyz.2 hxy.2⟩⟩
/-- The actual imaginary quotient, including its one infinity class. Ordered-group operations are not asserted by this definition alone. -/ def GammaTop := Quotient (valueSetoid (M := M))
def vrv (t : CanonicalRV.RVSort M) : GammaTop (M := M) := Quotient.mk _ t
def infinity : GammaTop (M := M) := vrv ⟨iRVZero, rv_zero_mem hM⟩
theorem vrv_surjective : Function.Surjective (vrv (M := M)) := by sorry
theorem vrv_eq_infinity_iff (t : CanonicalRV.RVSort M) : vrv t = infinity (M := M) ↔ t.val = iRVZero := by sorry
/-- The genuine value-group carrier excludes the absorbing infinity class. -/ def Gamma := { γ : GammaTop (M := M) // γ ≠ infinity }
theorem vf_value_eq_iff {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (v : Valuation (VFType (M := M)) Γ) (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y) (x y : VFType (M := M)) : vrv (CanonicalRV.encodedRv x) = vrv (CanonicalRV.encodedRv y) ↔ v x = v y := by sorry
end SpecialTransformations.Section3.Values
end
section
reset_statement_module_caches set_option autoImplicit true
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.Values
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
def gammaOf (t : CanonicalRV.RVSort M) (ht : t.val ≠ iRVZero) : Gamma (M := M) := ⟨vrv t, fun h => ht ((vrv_eq_infinity_iff t).mp h)⟩
def gammaPullback (V : Set (Gamma (M := M))) : Set M := {t | ∃ hRV : iRV t, ∃ h0 : t ≠ iRVZero, gammaOf ⟨t, hRV⟩ h0 ∈ V}
end SpecialTransformations.Section3.Values
end
section
reset_statement_module_caches set_option autoImplicit true
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer MonoidWithZeroHom
namespace SpecialTransformations.Section3.Values
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv
noncomputable def valueEquiv : GammaTop (M := M) ≃ ValueGroup₀ (.ofClass v) := CanonicalRV.equivOfSameFibers (fun x : VFType (M := M) => vrv (CanonicalRV.encodedRv x)) v.restrict (vrv_surjective.comp CanonicalRV.encodedRv_surjective) (ValueGroup₀.restrict₀_surjective (.ofClass v)) (fun x y => (vf_value_eq_iff v hv x y).trans v.restrict_inj.symm)
end SpecialTransformations.Section3.Values
end
section
reset_statement_module_caches set_option autoImplicit true
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Values
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- An internal compatible valuation presentation. This makes no choice of RV representatives as parameters and does not extend the base S. -/ noncomputable def presentationType : Type := Classical.choose (VFValued.exists_valuation_predV (M := M))
noncomputable instance presentationOrder : LinearOrderedCommGroupWithZero (presentationType (M := M)) := Classical.choose (Classical.choose_spec (VFValued.exists_valuation_predV (M := M)))
noncomputable def presentationValuation : Valuation (VFType (M := M)) (presentationType (M := M)) := Classical.choose (Classical.choose_spec (Classical.choose_spec (VFValued.exists_valuation_predV (M := M))))
theorem presentation_compatible (x y : VFType (M := M)) : VFValued.predV x y ↔ presentationValuation x ≤ presentationValuation y := by sorry
noncomputable def paperValueEquiv : GammaTop (M := M) ≃ OrderDual (MonoidWithZeroHom.ValueGroup₀ (.ofClass (presentationValuation (M := M)))) := valueEquiv presentationValuation presentation_compatible
end SpecialTransformations.Section3.Values
end
section
reset_statement_module_caches set_option autoImplicit true
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Values
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- The zero of this group-with-zero is the paper's infinity. Its order is reversed, so no ordered-group-with-zero instance asserting zero-minimality is introduced. The transfer follows Mathlib's Apache-2.0 Equiv transfer pattern in Algebra/GroupWithZero/TransferInstance.lean (Johannes Hoelzl) and uses Algebra/GroupWithZero/InjSurj.lean. -/ noncomputable instance gammaTopGroup : CommGroupWithZero (GammaTop (M := M)) := by
  let e := paperValueEquiv (M := M)
  letI := e.zero
  letI := e.one
  letI := e.mul
  letI := e.Inv
  letI := e.div
  letI := e.pow ℕ
  letI := e.pow ℤ
  apply e.injective.commGroupWithZero e <;> intros <;> exact e.apply_symm_apply _
noncomputable instance gammaTopOrder : LinearOrder (GammaTop (M := M)) := by classical exact (paperValueEquiv (M := M)).linearOrder
theorem infinity_eq_zero : infinity (M := M) = (0 : GammaTop (M := M)) := by sorry
noncomputable def gammaTopUnitsEquiv : Gamma (M := M) ≃ (GammaTop (M := M))ˣ where
  toFun γ := Units.mk0 γ.val (fun h => γ.property (h.trans infinity_eq_zero.symm))
  invFun u := ⟨u.val, fun h => Units.ne_zero u (h.trans infinity_eq_zero)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Units.ext rfl
/-- Gamma inherits the reversed order on its actual non-infinity subtype. -/ noncomputable instance gammaOrder : LinearOrder (Gamma (M := M)) := inferInstanceAs (LinearOrder { γ : GammaTop (M := M) // γ ≠ infinity })
noncomputable instance gammaGroup : CommGroup (Gamma (M := M)) := (gammaTopUnitsEquiv (M := M)).commGroup
end SpecialTransformations.Section3.Values
end
section
reset_statement_module_caches set_option autoImplicit true
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
open Values
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- Real codes for Gamma elements are all nonzero RV representatives. There is no chosen section in a parameter base. -/ def Code := { t : CanonicalRV.RVSort M // t.val ≠ iRVZero }
def raw (t : Code (M := M)) : M := t.val.val
def value (t : Code (M := M)) : Gamma (M := M) := gammaOf t.val t.property
theorem value_surjective : Function.Surjective (value (M := M)) := by sorry
/-- Used only inside proofs of surjectivity and descent. Definability of objects with Gamma parameters must use all codes and their invariance. -/ noncomputable def representative (γ : Gamma (M := M)) : Code (M := M) := Classical.choose (value_surjective γ)
def rawTuple {n : ℕ} (t : Fin n → Code (M := M)) : Fin n → M := fun i => raw (t i)
def values {n : ℕ} (t : Fin n → Code (M := M)) : Fin n → Gamma (M := M) := fun i => value (t i)
def Proper {n : ℕ} (a : Fin n → M) : Prop := ∀ i, iRV (a i) ∧ a i ≠ iRVZero
noncomputable def representatives {n : ℕ} (γ : Fin n → Gamma (M := M)) : Fin n → Code (M := M) := fun i => representative (γ i)
end SpecialTransformations.Section3.GammaParameters
end
section
reset_statement_module_caches set_option autoImplicit true
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- A genuine first-order relation with Gamma inputs, represented by its full invariant preimage on nonzero RV codes. Definability uses the normalized released LRV structure; no representative is named in the real base S. -/ structure Relation (S : Set M) (k n : ℕ) (sn : Fin n → SortTag) where
  carrier : Set ((Fin k → M) × (Fin n → M))
  definable : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin k ⊕ Fin n) {z | (z ∘ Sum.inl, z ∘ Sum.inr) ∈ carrier}
  proper : ∀ p ∈ carrier, Proper p.1 ∧ ∀ i, sortEval (sn i) (p.2 i)
  invariant : ∀ t u : Fin k → Code (M := M), values t = values u → ∀ b : Fin n → M, (rawTuple t, b) ∈ carrier ↔ (rawTuple u, b) ∈ carrier
namespace Relation
variable {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
def fibre (R : Relation S k n sn) (γ : Fin k → Values.Gamma (M := M)) : Set (Fin n → M) := {b | (rawTuple (representatives γ), b) ∈ R.carrier}
end Relation
/-- Definability over a finite tuple of actual Gamma parameters. The relation has a full first-order invariant preimage, not a chosen section. -/ def DefinableWith (S : Set M) {k n : ℕ} (γ : Fin k → Values.Gamma (M := M)) (sn : Fin n → SortTag) (A : Set (Fin n → M)) : Prop := ∃ R : Relation S k n sn, R.fibre γ = A
/-- A base in the real sorts together with its genuinely imaginary names. -/ structure Base where
  real : Set M
  gamma : Set (Values.Gamma (M := M))
def DefinableOverBase (B : Base (M := M)) {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → M)) : Prop := ∃ k, ∃ γ : Fin k → Values.Gamma (M := M), (∀ i, γ i ∈ B.gamma) ∧ DefinableWith B.real γ sn A
def DefinableAtBase (B : Base (M := M)) (σ : SortTag) (A : Set M) : Prop := DefinableOverBase B (fun _ : Fin 1 => σ) {z | z 0 ∈ A}
def GammaDefinableOverBase (B : Base (M := M)) (A : Set (Values.Gamma (M := M))) : Prop := DefinableAtBase B .rv (Values.gammaPullback A)
def GammaDefinableClosureAtBase (B : Base (M := M)) (γ : Values.Gamma (M := M)) : Prop := GammaDefinableOverBase B { γ }
end SpecialTransformations.Section3.GammaParameters
end
section
reset_statement_module_caches set_option autoImplicit true
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M]
def NonzeroRV (x : M) : Prop := iRV x ∧ x ≠ iRVZero
end SpecialTransformations.Section3.GammaParameters
end
section
reset_statement_module_caches set_option autoImplicit true
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
namespace GammaParameters
/-- Total semantic decoding used only to state full real-code preimages. Definability is always asserted for the entire guarded relation, never for a fictitious first-order language structure on the Gamma carrier. -/ noncomputable def codeValue (a : M) : Values.Gamma (M := M) := if h : NonzeroRV a then value ⟨⟨a, h.1⟩, h.2⟩ else 1
end GammaParameters
end SpecialTransformations.Section3
end
section
reset_statement_module_caches set_option autoImplicit true
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
theorem small_union_range_carrier {α : Type} {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (S : Set α) (hS : Cardinal.mk S < κ) {n : ℕ} (a : Fin n → α) : Cardinal.mk ↥(S ∪ Set.range a) < κ := by sorry
end SpecialTransformations.Section3.GammaParameters
end
section
reset_statement_module_caches set_option autoImplicit true
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Section3
namespace SpecialTransformations.Section4
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
abbrev Space := @DefinableGeometry.Space LRV M (CanonicalStructure.normalize (M := M))
def gammaSpace : Space (M := M) := by
  let X := Values.Gamma (M := M)
  let D : Set (Fin 1 → M) := {z | iRV (z 0) ∧ z 0 ≠ iRVZero}
  let dec (z : D) : X := Values.gammaOf ⟨z.val 0,z.property.1⟩ z.property.2
  letI := CanonicalStructure.normalize (M := M)
  exact {
    Carrier := X
    Index := Fin 1
    finiteIndex := inferInstance
    domain := D
    domain_definable := by sorry
    decode := dec
    onto := by sorry
    diagonal_definable := by sorry }
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `SpecialTransformations.Section4.gammaSpace 29)
end SpecialTransformations.Section4
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
namespace DiamondIntegral.Section2
variable (M : Type) [LRV.Structure M]
abbrev VF := VFType (M := M)
abbrev RVInfinity := CanonicalRV.RVSort M
variable [hM : M ⊨ Axioms.ACVF]
def rvZero : RVInfinity M := ⟨iRVZero, rv_zero_mem hM⟩
abbrev RV := { t : RVInfinity M // t ≠ rvZero M }
abbrev Gamma := Values.Gamma (M := M)
abbrev ParameterBase := GammaParameters.Base (M := M)
/-- Mixed ambient coordinates, including zero/infinity RV tags. -/ abbrev Mixed (n m : ℕ) := (Fin n → VF M) × (Fin m → RVInfinity M)
def rv : VF M → RVInfinity M := CanonicalRV.encodedRv
def tupleRV {n : ℕ} (a : Fin n → VF M) : Fin n → RVInfinity M := fun i => rv M (a i)
end DiamondIntegral.Section2
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Section3
namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- Two distinct Gamma values definable over the ground base. This states nontriviality using actual quotient values, without selecting RV lifts. For a language-substructure base, a bridge from its own nontrivial value group must supply these definable names. -/ def NontrivialDefinableGamma (B : ParameterBase M) : Prop := ∃ γ δ : Gamma M, GammaParameters.GammaDefinableClosureAtBase B γ ∧ GammaParameters.GammaDefinableClosureAtBase B δ ∧ γ ≠ δ
/-- Enlarging the named base preserves its nontrivial definable value group. -/ theorem NontrivialDefinableGamma.mono {B C : ParameterBase M} (hΓ : NontrivialDefinableGamma B) (hr : B.real ⊆ C.real) (hg : B.gamma ⊆ C.gamma) : NontrivialDefinableGamma C := by sorry
end DiamondIntegral.Section2
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Section3
namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
noncomputable def rvFiniteValue (t : RV M) : Gamma M := Values.gammaOf t.val (fun he => t.property (Subtype.ext he))
end DiamondIntegral.Section2
end
section
reset_statement_module_caches set_option autoImplicit false
open FirstOrder FirstOrder.Language SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {P Q : Space L M} {S : Set M} {p : P.Carrier}
def ImaginaryDefinable (P : Space L M) (p : P.Carrier) (Q : Space L M) (S : Set M) (A : Set Q.Carrier) : Prop := ∃ R : Set (P.prod Q).Carrier, (P.prod Q).Definable S R ∧ ∀ x, x ∈ A ↔ (p, x) ∈ R
end DiamondIntegral.Section3
end
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
namespace SpecialTransformations.Section8
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
theorem normalize_eq_of_isCanonical (hc : CanonicalStructure.IsCanonical (M := M)) : @CanonicalStructure.normalize M sM = sM := by sorry
end SpecialTransformations.Section8
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
noncomputable section
namespace DiamondIntegral.Section3
/-- Change only the proof of definability, keeping the presentation's carrier, real codes and decoding function literally unchanged. -/ def rebaseSpace {L : Language} {M : Type} {s t : L.Structure M} (h : s = t) (P : @Space L M s) : @Space L M t where
  Carrier := @Space.Carrier L M s P
  Index := @Space.Index L M s P
  finiteIndex := @Space.finiteIndex L M s P
  domain := @Space.domain L M s P
  domain_definable := by cases h; exact @Space.domain_definable L M s P
  decode := @Space.decode L M s P
  onto := @Space.onto L M s P
  diagonal_definable := by cases h; exact @Space.diagonal_definable L M s P
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}
/-- The existing imaginary Gamma presentation with its original actual Gamma carrier and every nonzero RV representative. Only the definability proof is rebased from the normalization of a canonical structure. -/ def volumeGammaSpace (hc : CanonicalStructure.IsCanonical (M := M)) : Space LRV M := rebaseSpace (normalize_eq_of_isCanonical hc) (@gammaSpace M sM hM)
end DiamondIntegral.Section3
end
end
section
reset_statement_module_caches set_option autoImplicit false
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {Q : Space LRV M}
def GammaGroundDefinable (hc : CanonicalStructure.IsCanonical (M := M)) (B : GammaParameters.Base (M := M)) (Q : Space LRV M) (A : Set Q.Carrier) : Prop := ∃ k, ∃ γ : Fin k → Values.Gamma (M := M), (∀ i, γ i ∈ B.gamma) ∧ ImaginaryDefinable ((volumeGammaSpace hc).power (Fin k)) γ Q B.real A
theorem GammaGroundDefinable.of_real {A : Set Q.Carrier} (hA : Q.Definable B.real A) : GammaGroundDefinable hc B Q A := by sorry
theorem GammaGroundDefinable.inter {A D : Set Q.Carrier} (hA : GammaGroundDefinable hc B Q A) (hD : GammaGroundDefinable hc B Q D) : GammaGroundDefinable hc B Q (A ∩ D) := by sorry
theorem GammaGroundDefinable.compl {A : Set Q.Carrier} (hA : GammaGroundDefinable hc B Q A) : GammaGroundDefinable hc B Q Aᶜ := by sorry
structure GammaGroundDefSet (hc : CanonicalStructure.IsCanonical (M := M)) (B : GammaParameters.Base (M := M)) (Q : Space LRV M) where
  carrier : Set Q.Carrier
  definable : GammaGroundDefinable hc B Q carrier
end DiamondIntegral.Section3
end
end
section
reset_statement_module_caches set_option autoImplicit false
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {Q R : Space LRV M}
def GammaGroundDefSet.ofReal (A : DefSet Q ground.real) : GammaGroundDefSet hc ground Q := ⟨A.carrier, GammaGroundDefinable.of_real A.definable⟩
def GammaGroundDefSet.univ (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (Q : Space LRV M) : GammaGroundDefSet hc ground Q := .ofReal (DefSet.univ Q ground.real)
def GammaGroundDefSet.inter (A B : GammaGroundDefSet hc ground Q) : GammaGroundDefSet hc ground Q := ⟨A.carrier ∩ B.carrier, A.definable.inter B.definable⟩
def GammaGroundDefSet.compl (A : GammaGroundDefSet hc ground Q) : GammaGroundDefSet hc ground Q := ⟨A.carrierᶜ, A.definable.compl⟩
def GammaGroundDefSet.sdiff (A B : GammaGroundDefSet hc ground Q) : GammaGroundDefSet hc ground Q := A.inter B.compl
end DiamondIntegral.Section3
end
end
section
reset_statement_module_caches set_option autoImplicit false
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {Q R T U : Space LRV M} {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
instance gammaGroundDefSetCoeSort {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {P : Space LRV M} : CoeSort (GammaGroundDefSet hc B P) Type := ⟨fun A => A.carrier⟩
structure GammaGroundMap (A : GammaGroundDefSet hc ground Q) (B : GammaGroundDefSet hc ground R) where
  toFun : A → B
  graph_definable : GammaGroundDefinable hc ground (Q.prod R) {z | ∃ a : A, a.val = z.1 ∧ (toFun a).val = z.2}
instance gammaGroundMapCoeFun {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R} : CoeFun (GammaGroundMap A B) (fun _ => A → B) := ⟨GammaGroundMap.toFun⟩
end DiamondIntegral.Section3
end
end
section
reset_statement_module_caches set_option autoImplicit false
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {Q R T U : Space LRV M} {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
structure GammaGroundBijection (A : GammaGroundDefSet hc ground Q) (B : GammaGroundDefSet hc ground R) where
  map : GammaGroundMap A B
  bijective : Function.Bijective map
end DiamondIntegral.Section3
end
end
section
reset_statement_module_caches set_option autoImplicit false
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {Q R T U : Space LRV M} {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
def GammaGroundMap.FiniteFibres {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R} (f : GammaGroundMap A B) : Prop := ∀ b : B, {a : A | f a = b}.Finite
end DiamondIntegral.Section3
end
end
section
reset_statement_module_caches set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace DiamondIntegral.Section4.GammaOrderLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
def GammaDefinable (B : Base (M := M)) {n : ℕ} (P : Set (Fin n → Values.Gamma (M := M))) : Prop := DefinableOverBase B (fun _ : Fin n => .rv) {z | Proper z ∧ (fun i => codeValue (M := M) (z i)) ∈ P}
end DiamondIntegral.Section4.GammaOrderLogic
end
end
section
reset_statement_module_caches set_option autoImplicit true
open Classical
namespace DiamondIntegral.Section4
inductive EulerKind where | geometric | bounded deriving DecidableEq
def EulerKind.lineValue : EulerKind → ℤ | .geometric => -1 | .bounded => 1
def EulerKind.rayValue : EulerKind → ℤ | .geometric => -1 | .bounded => 0
end DiamondIntegral.Section4
end
section
reset_statement_module_caches set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace DiamondIntegral.Section4.GammaGroupNames
open GammaOrderLogic
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
theorem one_definable_base (B : Base (M := M)) : GammaDefinableClosureAtBase B (1 : Values.Gamma (M := M)) := by sorry
end DiamondIntegral.Section4.GammaGroupNames
end
end
section
reset_statement_module_caches set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
structure GammaGroundRVObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) where
  arity : ℕ
  domain : GammaGroundDefSet hc ground (rawRVSpace (M := M) arity)
  volume : GammaGroundMap domain (GammaGroundDefSet.univ hc ground (rawRVSpace k))
  finite : volume.FiniteFibres
  nonzero : ∀ a : domain, ∀ i, ((volume a).val i).val ≠ iRVZero
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}
instance gammaGroundRVObjectGroupoid : Groupoid.{0} (GammaGroundRVObject hc ground k) := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `DiamondIntegral.Section3.gammaGroundRVObjectGroupoid 27)
def gammaGroundResProperty : ObjectProperty (GammaGroundRVObject hc ground k) := fun U => ((fun t i => Values.vrv (t i)) '' U.domain.carrier).Finite
abbrev GammaGroundRESObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) := (gammaGroundResProperty (hc := hc) (ground := ground) (k := k)).FullSubcategory
end DiamondIntegral.Section3
end
end
section
reset_statement_module_caches set_option autoImplicit true
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- The VF field and the RV representatives of the paper's base. The field requirement is the manuscript's standing substructure convention. -/ structure VFGeneratedFieldBase (S : LRV.Substructure M) extends VFFieldBase (S : Set M) where
  rv_lift : ∀ t ∈ S, iRV t → ∃ a : field, iRv a.val.val = t
end DiamondIntegral.Section2
end
section
reset_statement_module_caches set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace DiamondIntegral.Section4.GammaCellSections
open GammaOrderLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
def graphCell {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M))) (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) : Set (Fin (n + 1) → Values.Gamma (M := M)) := {z | Fin.tail z ∈ C ∧ z 0 = T (Fin.tail z)}
def bandCell {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M))) (l u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) : Set (Fin (n + 1) → Values.Gamma (M := M)) := {z | Fin.tail z ∈ C ∧ l (Fin.tail z) < z 0 ∧ z 0 < u (Fin.tail z)}
end DiamondIntegral.Section4.GammaCellSections
end
end
section
reset_statement_module_caches set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace DiamondIntegral.Section4.GammaCellUnboundedSections
open GammaOrderLogic GammaCellSections
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
def upperRayCell {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M))) (l : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) : Set (Fin (n + 1) → Values.Gamma (M := M)) := {z | Fin.tail z ∈ C ∧ l (Fin.tail z) < z 0}
def lowerRayCell {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M))) (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) : Set (Fin (n + 1) → Values.Gamma (M := M)) := {z | Fin.tail z ∈ C ∧ z 0 < u (Fin.tail z)}
def lineCell {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M))) : Set (Fin (n + 1) → Values.Gamma (M := M)) := {z | Fin.tail z ∈ C}
end DiamondIntegral.Section4.GammaCellUnboundedSections
end
end
section
reset_statement_module_caches set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters DiamondIntegral.Section4 GammaOrderLogic GammaCellSections GammaCellUnboundedSections
inductive CylindricalShape : ℕ → Type where | base : CylindricalShape 0 | graph {n : ℕ} : CylindricalShape n → CylindricalShape (n + 1) | band {n : ℕ} : CylindricalShape n → CylindricalShape (n + 1) | upperRay {n : ℕ} : CylindricalShape n → CylindricalShape (n + 1) | lowerRay {n : ℕ} : CylindricalShape n → CylindricalShape (n + 1) | line {n : ℕ} : CylindricalShape n → CylindricalShape (n + 1)
def CylindricalShape.eulerValue (k : EulerKind) : {n : ℕ} → CylindricalShape n → ℤ | _, .base => 1 | _, .graph s => s.eulerValue k | _, .band s => -s.eulerValue k | _, .upperRay s => k.rayValue * s.eulerValue k | _, .lowerRay s => k.rayValue * s.eulerValue k | _, .line s => k.lineValue * s.eulerValue k
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
inductive ShapedGammaCell (B : Base (M := M)) : (n : ℕ) → Set (Fin n → Values.Gamma (M := M)) → CylindricalShape n → Prop where | base : ShapedGammaCell B 0 Set.univ .base | graph {n C s} (hc : ShapedGammaCell B n C s) (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hR : GammaDefinable B (graphCell C T)) : ShapedGammaCell B (n + 1) (graphCell C T) (.graph s) | band {n C s} (hc : ShapedGammaCell B n C s) (l u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hlu : ∀ y ∈ C, l y < u y) (hR : GammaDefinable B (bandCell C l u)) : ShapedGammaCell B (n + 1) (bandCell C l u) (.band s) | upperRay {n C s} (hc : ShapedGammaCell B n C s) (l : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hR : GammaDefinable B (upperRayCell C l)) : ShapedGammaCell B (n + 1) (upperRayCell C l) (.upperRay s) | lowerRay {n C s} (hc : ShapedGammaCell B n C s) (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hR : GammaDefinable B (lowerRayCell C u)) : ShapedGammaCell B (n + 1) (lowerRayCell C u) (.lowerRay s) | line {n C s} (hc : ShapedGammaCell B n C s) (hR : GammaDefinable B (lineCell C)) : ShapedGammaCell B (n + 1) (lineCell C) (.line s)
theorem ShapedGammaCell.definable {B : Base (M := M)} {n : ℕ} {s : CylindricalShape n} {C : Set (Fin n → Values.Gamma (M := M))} (h : ShapedGammaCell B n C s) : GammaDefinable B C := by sorry
end DiamondIntegral.Section5
end
end
section
reset_statement_module_caches set_option autoImplicit false
open FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Section3
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
structure GammaGroundContext (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] where
  model00 : M ⊨ Axioms.ACVF00
  κ : Cardinal
  uncountable : Cardinal.aleph0 < κ
  saturated : Saturated M κ
  homogeneous : StronglyHomogeneous M κ
  real : LRV.Substructure M
  fieldBase : Section2.VFGeneratedFieldBase real
  gamma : Subgroup (Values.Gamma (M := M))
  values_mem : ∀ t : Section2.RV M, t.val.val ∈ (real : Set M) → Section2.rvFiniteValue t ∈ gamma
  small_real : Cardinal.mk real < κ
  small_gamma : Cardinal.mk gamma < κ
  nontrivial_gamma : ∃ γ : gamma, γ.val ≠ 1
def GammaGroundContext.base (C : GammaGroundContext M) : GammaParameters.Base (M := M) := ⟨(C.real : Set M), (C.gamma : Set (Values.Gamma (M := M)))⟩
end DiamondIntegral.Section3
end
end
section
reset_statement_module_caches set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)}
/-- The context's nontrivial Gamma names suffice; no nontrivial value or RV representative in its VF-generated real part is required. -/ theorem GammaGroundContext.nontrivial_definable_gamma (C : GammaGroundContext M) : Section2.NontrivialDefinableGamma C.base := by sorry
end DiamondIntegral.Section3
end
end
section
reset_statement_module_caches set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
structure GammaGroundFiniteVFObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) where
  vfArity : ℕ
  rvArity : ℕ
  domain : GammaGroundDefSet hc ground (rawMixedSpace (M := M) vfArity rvArity)
  finite : ∀ a : Fin vfArity → Section2.VF M, {t | (a, t) ∈ domain.carrier}.Finite
end DiamondIntegral.Section3
end
end
section
reset_statement_module_caches set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}
def nativeMixedCode (q : Section2.Mixed M n r) : Fin (n + r) → M := Fin.append (vfValues q.1) (rvValues q.2)
def nativeMixedDomain (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) : Set (Fin (n + r) → M) := nativeMixedCode '' A.carrier
end DiamondIntegral.Section5
end
end
section
reset_statement_module_caches set_option autoImplicit true
noncomputable section
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters DiamondIntegral.Section3 DiamondIntegral.Section4
namespace FubiniStatement
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
/-- The ordinary Cartesian product carrier, concatenating its RV coordinates. -/ def productCarrier {k l : ℕ} (U : GammaGroundRVObject hc B k) (V : GammaGroundRVObject hc B l) := Set.range (fun x : U.domain × V.domain => Fin.append x.1.val x.2.val)
/-- A labelled Cartesian product, whose entire underlying carrier is fixed. -/ def rvProduct {k l : ℕ} (U : GammaGroundRVObject hc B k) (V : GammaGroundRVObject hc B l) : { W : GammaGroundRVObject hc B (k + l) // W.arity = U.arity + V.arity ∧ HEq W.domain.carrier (productCarrier U V) } := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `FubiniStatement.rvProduct 30)
/-- A Cartesian product of finite-value-support objects with its full carrier. -/ def resProduct {k l : ℕ} (U : GammaGroundRESObject hc B k) (V : GammaGroundRESObject hc B l) : { W : GammaGroundRESObject hc B (k + l) // W.obj.arity = U.obj.arity + V.obj.arity ∧ HEq W.obj.domain.carrier (productCarrier U.obj V.obj) } := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `FubiniStatement.resProduct 31)
/-- Restriction to the specified definable subset; no new underlying points. -/ def rvRestrict {k : ℕ} (U : GammaGroundRVObject hc B k) (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.arity)) (hX : X.carrier ⊆ U.domain.carrier) : { W : GammaGroundRVObject hc B k // W.arity = U.arity ∧ HEq W.domain.carrier X.carrier } := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `FubiniStatement.rvRestrict 28)
/-- Restriction preserves finite value support and has exactly the specified carrier. -/ def resRestrict {k : ℕ} (U : GammaGroundRESObject hc B k) (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.obj.arity)) (hX : X.carrier ⊆ U.obj.domain.carrier) : { W : GammaGroundRESObject hc B k // W.obj.arity = U.obj.arity ∧ HEq W.obj.domain.carrier X.carrier } := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `FubiniStatement.resRestrict 29)
/-- The zero-dimensional point, the unit of the ungraded RES ring. -/ def resUnit (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) : { U : GammaGroundRESObject hc B 0 // U.obj.arity = 0 ∧ HEq U.obj.domain.carrier (Set.univ : Set (Fin 0 → CanonicalRV.RVSort M)) } := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `FubiniStatement.resUnit 30)
/-- The empty RV object, with an arbitrary label degree and no underlying points. -/ def rvEmpty (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) : { U : GammaGroundRVObject hc B k // U.arity = 0 ∧ HEq U.domain.carrier (∅ : Set (Fin 0 → CanonicalRV.RVSort M)) } := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `FubiniStatement.rvEmpty 28)
/-- The positive RV lift retains all RV coordinates and imposes precisely rv(x) = volume(u), over the unchanged parameter base. -/ def vfLift {k : ℕ} (U : GammaGroundRVObject hc B k) : { D : GammaGroundDefSet hc B (rawMixedSpace (M := M) k U.arity) // D.carrier = {q | ∃ u : U.domain, u.val = q.2 ∧ (U.volume u).val = DiamondIntegral.Section2.tupleRV M q.1} } := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `FubiniStatement.vfLift 29)
/-- The actual map fibre over the raw mixed point, with precisely that tuple adjoined to the real base and no enlargement of its Gamma parameters. -/ def mapFibre {n r p q : ℕ} {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)} {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C) (z : Fin (p + q) → M) : { D : GammaGroundDefSet hc ⟨B.real ∪ Set.range z, B.gamma⟩ (rawMixedSpace (M := M) n r) // D.carrier = {x | ∃ a : A, a.val = x ∧ DiamondIntegral.Section5.nativeMixedCode (f a).val = z} } := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `FubiniStatement.mapFibre 37)
end FubiniStatement
end
end
section
reset_statement_module_caches set_option autoImplicit true
noncomputable section
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
namespace FubiniStatement
/-- The complete carrier, code sort, code domain and decoding function of a presentation. Definability and surjectivity certificates are proof fields. -/ def spaceData {L : Language} {M : Type} [L.Structure M] (P : SpecialTransformations.DefinableGeometry.Space L M) : (X : Type) × (ι : Type) × (D : Set (ι → M)) × (D → X) := ⟨P.Carrier, P.Index, P.domain, P.decode⟩
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
/-- Gamma has all nonzero RV codes and decodes by the actual value quotient. -/ theorem gammaSpace_data : @spaceData LRV M (CanonicalStructure.normalize (M := M)) (gammaSpace (M := M)) = ⟨Values.Gamma (M := M), Fin 1, {z | iRV (z 0) ∧ z 0 ≠ iRVZero}, fun z => Values.gammaOf ⟨z.val 0, z.property.1⟩ z.property.2⟩ := by sorry
/-- Raw VF coordinates are coded by their underlying original-model elements. -/ theorem rawVFSpace_data (n : ℕ) : spaceData (rawVFSpace (M := M) n) = ⟨Fin n → VFType (M := M), Fin n, Set.range (vfValues (M := M) (n := n)), fun z => Classical.choose z.property⟩ := by sorry
/-- Raw RV coordinates have exactly the original RV-sort tuple carrier. -/ theorem rawRVSpace_data (n : ℕ) : spaceData (rawRVSpace (M := M) n) = ⟨Fin n → CanonicalRV.RVSort M, Fin n, Set.range (rvValues (M := M) (n := n)), fun z => Classical.choose z.property⟩ := by sorry
/-- The VF field structure is the original model's zero, one, addition and multiplication. Field laws determine its remaining operations uniquely. -/ theorem vfField_operations :
    let F := vfFieldOfModel (M := M)
    F.zero.val = iVFZero ∧ F.one.val = iVFOne ∧ (∀ a b, (F.add a b).val = iVFAdd a.val b.val) ∧ (∀ a b, (F.mul a b).val = iVFMul a.val b.val) := by sorry
open CategoryTheory DiamondIntegral.Section3 SpecialTransformations.Section3.GammaParameters
/-- The category decoration of RES objects has exactly the actual underlying definable bijections as its morphisms; labels are forgotten. -/ theorem rvGroupoid_hom {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ} (U V : GammaGroundRVObject hc B k) : (U ⟶ V) = GammaGroundBijection U.domain V.domain := by sorry
end FubiniStatement
end
end
section
reset_statement_module_caches set_option autoImplicit true
noncomputable section
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters DiamondIntegral.Section3 DiamondIntegral.Section4
namespace FubiniStatement
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
/-- Actual finite-value-support RES objects; the label degree is retained only to encode an object, and is forgotten by the relation below. -/ abbrev RESGenerator (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) := Sigma (GammaGroundRESObject hc B)
abbrev RESRaw (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) := FreeCommRing (RESGenerator hc B)
def resSymbol {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ} (U : GammaGroundRESObject hc B k) : RESRaw hc B := FreeCommRing.of ⟨k, U⟩
/-- A full one-dimensional RV value fibre, specified by its actual carrier. -/ def IsValueLine {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ} (U : GammaGroundRESObject hc B k) (α : Values.Gamma (M := M)) : Prop := U.obj.arity = 1 ∧ ∀ u, u ∈ U.obj.domain.carrier ↔ ∀ i, Values.vrv (u i) = α.val
/-- A genuine full value fibre, with its carrier specification built into its type. Different finite-to-one labels have the same ungraded class. -/ def valueLineObject (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (α : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) : { U : GammaGroundRESObject hc B 1 // IsValueLine U α } := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `FubiniStatement.valueLineObject 44)
/-- Scissors, products, underlying definable bijections and the value-torsor relations, over the same original parameter base. -/ inductive RESRelation (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) : RESRaw hc B → Prop | unit : RESRelation hc B (resSymbol (resUnit hc B).val - 1) | product {k l : ℕ} (U : GammaGroundRESObject hc B k) (V : GammaGroundRESObject hc B l) : RESRelation hc B (resSymbol (resProduct U V).val - resSymbol U * resSymbol V) | iso {k l : ℕ} (U : GammaGroundRESObject hc B k) (V : GammaGroundRESObject hc B l) (e : GammaGroundBijection U.obj.domain V.obj.domain) : RESRelation hc B (resSymbol U - resSymbol V) | empty {k : ℕ} (U : GammaGroundRESObject hc B k) (h : U.obj.domain.carrier = ∅) : RESRelation hc B (resSymbol U) | cut {k : ℕ} (U : GammaGroundRESObject hc B k) (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.obj.arity)) (hX : X.carrier ⊆ U.obj.domain.carrier) : RESRelation hc B (resSymbol U - resSymbol (resRestrict U X hX).val - resSymbol (resRestrict U (U.obj.domain.sdiff X) (fun _ h => h.1)).val) | valueLine (α : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) : RESRelation hc B (resSymbol (valueLineObject hc B α hα).val - resSymbol (valueLineObject hc B 1 (GammaGroupNames.one_definable_base B)).val)
def resIdeal (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) : Ideal (RESRaw hc B) := Ideal.span {r | RESRelation hc B r}
/-- The intrinsic ungraded reduced RES ring of the actual definable sets. -/ abbrev RESRing (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) := RESRaw hc B ⧸ resIdeal hc B
def resClass {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ} (U : GammaGroundRESObject hc B k) : RESRing hc B := Ideal.Quotient.mk _ (resSymbol U)
end FubiniStatement
end
end
section
reset_statement_module_caches set_option autoImplicit true
noncomputable section
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters DiamondIntegral.Section3 DiamondIntegral.Section4 DiamondIntegral.Section5
namespace FubiniStatement
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
/-- The full RV inverse image of an actual Gamma set, with no choice of representatives or valuation section. -/ def gammaLiftDomain {n : ℕ} (T : Set (Fin n → Values.Gamma (M := M))) : Set (Fin n → CanonicalRV.RVSort M) := {u | ∃ γ ∈ T, ∀ i, Values.vrv (u i) = (γ i).val}
/-- A finite-to-one labelled RV representative of the full Gamma inverse image. Its entire carrier is specified, and the ungraded value forgets labels. -/ def gammaLiftObject (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) {n : ℕ} (T : Set (Fin n → Values.Gamma (M := M))) (hT : GammaOrderLogic.GammaDefinable B T) : { U : GammaGroundRVObject hc B n // U.arity = n ∧ HEq U.domain.carrier (gammaLiftDomain T) } := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `FubiniStatement.gammaLiftObject 44)
def torusClass (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) : RESRing hc B := resClass (valueLineObject hc B 1 (GammaGroupNames.one_definable_base B)).val
/-- The ordinary bounded RES retraction, characterized by actual underlying bijections, scissors and monomial cylindrical-cell values. No Fubini law is part of this definition. -/ structure BoundedRVValues (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) where
  value : ∀ {k : ℕ}, GammaGroundRVObject hc B k → RESRing hc B
  bijection : ∀ {k l : ℕ} (U : GammaGroundRVObject hc B k) (V : GammaGroundRVObject hc B l), GammaGroundBijection U.domain V.domain → value U = value V
  empty : ∀ k : ℕ, value (rvEmpty hc B k).val = 0
  cut : ∀ {k : ℕ} (U : GammaGroundRVObject hc B k) (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.arity)) (hX : X.carrier ⊆ U.domain.carrier), value (rvRestrict U X hX).val + value (rvRestrict U (U.domain.sdiff X) (fun _ h => h.1)).val = value U
  monomialCell : ∀ {k n : ℕ} (V : GammaGroundRESObject hc B k) (T : Set (Fin n → Values.Gamma (M := M))) (shape : CylindricalShape n) (hcell : ShapedGammaCell B n T shape), value (rvProduct V.obj (gammaLiftObject hc B T hcell.definable).val).val = resClass V * torusClass hc B ^ n * (shape.eulerValue .bounded : RESRing hc B)
/-- The characterized bounded retraction, constructed from the checked native one and the proved intrinsic-ring comparison. -/ def boundedRVValues (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (hΓ : DiamondIntegral.Section2.NontrivialDefinableGamma B) : BoundedRVValues hc B := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `FubiniStatement.boundedRVValues 65)
end FubiniStatement
end
end
section
reset_statement_module_caches set_option autoImplicit true
noncomputable section
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters DiamondIntegral.Section3 DiamondIntegral.Section4 DiamondIntegral.Section5
namespace FubiniStatement
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
/-- The bounded invariant of actual finite-RV-fibre VF objects, characterized by its value on every definable bijection to a positive RV lift. -/ structure BoundedVFValues (G : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M)) where
  value : GammaGroundFiniteVFObject hc G.base → RESRing hc G.base
  lift_value : ∀ (A : GammaGroundFiniteVFObject hc G.base) {k : ℕ} (U : GammaGroundRVObject hc G.base k), GammaGroundBijection A.domain (vfLift U).val → value A = (boundedRVValues G.model00 G.uncountable.le G.saturated hc G.base G.small_real G.small_gamma G.nontrivial_definable_gamma).value U
/-- The canonical bounded invariant, constructed using the original-ground lifting theorem and the proved intrinsic reduced-RES comparison. -/ def boundedVFValues (G : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M)) : BoundedVFValues G hc := by sorry
run_cmd Lean.modifyEnv (fun env => Lean.setDefHeightOverride env `FubiniStatement.boundedVFValues 66)
/-- Equality of the bounded values of two fibres means equality on actual RV lifts over the original base with precisely the common point adjoined. -/ def FibreLiftEquality (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : DiamondIntegral.Section2.NontrivialDefinableGamma B)
    {n r m s p q : ℕ}
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {A' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}
    (f : GammaGroundMap A C) (f' : GammaGroundMap A' C) (z : Fin (p+q) → M) : Prop := ∃ k l : ℕ,
    ∃ U : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k,
    ∃ V : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ l,
      Nonempty (GammaGroundBijection (mapFibre f z).val (vfLift U).val) ∧
      Nonempty (GammaGroundBijection (mapFibre f' z).val (vfLift V).val) ∧
      (boundedRVValues h00 hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl)).value U =
      (boundedRVValues h00 hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl)).value V
/-- Forey–Yin Theorem 5.17: equality on every intrinsic parameter-relative fibre implies equality of the total bounded invariants. -/ theorem bounded_fubini {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M} (A A' : GammaGroundFiniteVFObject hc G.base) {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q)) (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C) (h : ∀ z ∈ nativeMixedDomain C, FibreLiftEquality G.model00 G.uncountable.le G.saturated G.small_real G.small_gamma G.nontrivial_definable_gamma f f' z) : (boundedVFValues G hc).value A = (boundedVFValues G hc).value A' := by sorry
end FubiniStatement
end
end
