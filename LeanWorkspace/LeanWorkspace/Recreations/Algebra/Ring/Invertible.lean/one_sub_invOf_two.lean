import Mathlib

open scoped Ring

variable {R : Type*}

theorem one_sub_invOf_two [Ring R] [Invertible (2 : R)] : 1 - (⅟2 : R) = ⅟2 := (isUnit_of_invertible (2 : R)).mul_right_inj.1 <| by
    rw [mul_sub, mul_invOf_self, mul_one, ← one_add_one_eq_two, add_sub_cancel_right]

