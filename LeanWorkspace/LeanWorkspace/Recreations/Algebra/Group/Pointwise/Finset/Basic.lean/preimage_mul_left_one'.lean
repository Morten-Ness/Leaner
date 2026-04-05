import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] {a b : α}

theorem preimage_mul_left_one' : preimage 1 (a⁻¹ * ·) (mul_right_injective _).injOn = {a} := by
  rw [Finset.preimage_mul_left_one, inv_inv]

