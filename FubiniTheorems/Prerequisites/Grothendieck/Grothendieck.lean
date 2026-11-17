import HilbertMathlib.Foundation.Grothendieck.ScissorGroupification

noncomputable section
namespace DiamondIntegral.Section3

/-- Distinct measured and unmeasured principal relations after groupification.
Here p is the degree-one point, b the punctured positive-value RV interval.
The extra degree-zero singleton belongs only to the unmeasured relation. -/
theorem unmeasured_relation_iff {R : Type v} [Ring R] (p b : R) :
    p - b - 1 = 0 ↔ p = b + 1 := by
  rw [sub_eq_zero, sub_eq_iff_eq_add, add_comm (1 : R) b]

theorem measured_relation_iff {R : Type v} [Ring R] (p b : R) :
    p - b = 0 ↔ p = b := sub_eq_zero

end DiamondIntegral.Section3
