import Mathlib

variable {α : Type u}

theorem invOf_mul [Monoid α] (a b : α) [Invertible a] [Invertible b] [Invertible (a * b)] :
    ⅟(a * b) = ⅟b * ⅟a := invOf_eq_right_inv (by simp [← mul_assoc])

