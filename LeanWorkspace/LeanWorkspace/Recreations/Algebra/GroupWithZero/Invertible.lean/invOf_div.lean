import Mathlib

open scoped Ring

variable {α : Type u}

variable [GroupWithZero α]

theorem invOf_div (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)] :
    ⅟(a / b) = b / a := invOf_eq_right_inv (by simp [← mul_div_assoc])

