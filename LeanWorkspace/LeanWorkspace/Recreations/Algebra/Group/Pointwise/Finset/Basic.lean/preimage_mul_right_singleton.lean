import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] {a b : α}

theorem preimage_mul_right_singleton :
    preimage {b} (· * a) (mul_left_injective _).injOn = {b * a⁻¹} := by
  classical rw [← Finset.image_mul_right', image_singleton]

