import Mathlib

open scoped Pointwise

variable {k : Type u₁} {G : Type u₂} [Semiring k]

variable [Mul G]

theorem support_single_mul_eq_image [DecidableEq G] (f : k[G]) {r : k}
    (hr : ∀ y, r * y = 0 ↔ y = 0) {x : G} (lx : IsLeftRegular x) :
    (single x r * f : k[G]).support = Finset.image (x * ·) f.support := by
  refine subset_antisymm (MonoidAlgebra.support_single_mul_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.support ∧ x * a = y := by grind
  simp [mul_apply, mem_support_iff.mp yf, hr, lx.eq_iff]

