import Mathlib

open scoped Pointwise

variable {k : Type u₁} {G : Type u₂} [Semiring k]

variable [Mul G]

theorem support_mul_single_eq_image [DecidableEq G] (f : k[G]) {r : k}
    (hr : ∀ y, y * r = 0 ↔ y = 0) {x : G} (rx : IsRightRegular x) :
    (f * single x r).support = Finset.image (· * x) f.support := by
  refine subset_antisymm (MonoidAlgebra.support_mul_single_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.support ∧ a * x = y := by grind
  simp only [mul_apply, mem_support_iff.mp yf, hr, mem_support_iff, sum_single_index,
    Finsupp.sum_ite_eq', Ne, not_false_iff, if_true, mul_zero, ite_self, rx.eq_iff]

