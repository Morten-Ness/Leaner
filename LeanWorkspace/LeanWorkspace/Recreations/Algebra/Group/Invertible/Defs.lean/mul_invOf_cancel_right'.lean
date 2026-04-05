import Mathlib

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem mul_invOf_cancel_right' {_ : Invertible b} : a * b * ⅟b = a := by
  simp [mul_assoc]
example {G} [Group G] (a b : G) : a * b * b⁻¹ = a := mul_inv_cancel_right a b

