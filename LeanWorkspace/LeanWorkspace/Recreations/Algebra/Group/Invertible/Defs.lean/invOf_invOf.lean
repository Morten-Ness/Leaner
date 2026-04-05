import Mathlib

variable {α : Type u}

theorem invOf_invOf [Monoid α] (a : α) [Invertible a] [Invertible (⅟a)] : ⅟(⅟a) = a := invOf_eq_right_inv (invOf_mul_self _)

