import Mathlib

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invOf_mul_cancel_left' {_ : Invertible a} : ⅟a * (a * b) = b := by
  rw [← mul_assoc, invOf_mul_self, one_mul]
example {G} [Group G] (a b : G) : a⁻¹ * (a * b) = b := inv_mul_cancel_left a b

