import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] {a b : α}

theorem preimage_mul_right_one : preimage 1 (· * b) (mul_left_injective _).injOn = {b⁻¹} := by
  classical rw [← Finset.image_mul_right', Finset.image_one, one_mul]

