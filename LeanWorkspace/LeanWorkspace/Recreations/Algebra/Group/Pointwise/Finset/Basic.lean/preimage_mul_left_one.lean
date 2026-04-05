import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] {a b : α}

theorem preimage_mul_left_one : preimage 1 (a * ·) (mul_right_injective _).injOn = {a⁻¹} := by
  classical rw [← Finset.image_mul_left', Finset.image_one, mul_one]

