import Mathlib

variable {α : Type u}

theorem commute_invOf {M : Type*} [One M] [Mul M] (m : M) [Invertible m] : Commute m (⅟m) := calc
    m * ⅟m = 1 := mul_invOf_self m
    _ = ⅟m * m := (invOf_mul_self m).symm

