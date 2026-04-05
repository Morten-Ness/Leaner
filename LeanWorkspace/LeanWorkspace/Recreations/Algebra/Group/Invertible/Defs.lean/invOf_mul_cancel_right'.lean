import Mathlib

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invOf_mul_cancel_right' {_ : Invertible b} : a * ⅟b * b = a := by
  simp [mul_assoc]
example {G} [Group G] (a b : G) : a * b⁻¹ * b = a := inv_mul_cancel_right a b

