/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/a3ef33e664e0a0725f0b04d9400bb7c8a1b8e95a/section%203/IntegerMonomialReindexing.lean
Original public declaration namespaces and source notices are retained.
Implementation ownership and the finite-laws split are recorded in SOURCE-MANIFEST.json.
-/
import HilbertMathlib.Foundation.FiniteCoordinates.IntegerMonomialMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {α β ι G : Type} [Fintype α] [Fintype β] [CommGroup G]

theorem integerMonomialMap_reindex_input (e : α ≃ β) (A : Matrix ι α ℤ) (z : β → G) :
    integerMonomialMap A (z ∘ e) = integerMonomialMap (fun i j => A i (e.symm j)) z := by
  funext i
  simpa only [integerMonomialMap,Function.comp_apply,Equiv.symm_apply_apply] using
    e.prod_comp (fun j => z j ^ A i (e.symm j))
end DiamondIntegral.Section3
