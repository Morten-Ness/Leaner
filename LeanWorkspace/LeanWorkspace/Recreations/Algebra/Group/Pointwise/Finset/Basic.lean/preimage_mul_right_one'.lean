import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] {a b : α}

theorem preimage_mul_right_one' : preimage 1 (· * b⁻¹) (mul_left_injective _).injOn = {b} := by
  rw [Finset.preimage_mul_right_one, inv_inv]

