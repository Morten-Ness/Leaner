import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] {a b : α}

theorem preimage_mul_left_singleton :
    preimage {b} (a * ·) (mul_right_injective _).injOn = {a⁻¹ * b} := by
  classical rw [← Finset.image_mul_left', image_singleton]

