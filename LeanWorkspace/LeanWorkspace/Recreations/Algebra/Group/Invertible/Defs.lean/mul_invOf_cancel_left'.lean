import Mathlib

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem mul_invOf_cancel_left' {_ : Invertible a} : a * (⅟a * b) = b := by
  rw [← mul_assoc, mul_invOf_self, one_mul]
example {G} [Group G] (a b : G) : a * (a⁻¹ * b) = b := mul_inv_cancel_left a b

