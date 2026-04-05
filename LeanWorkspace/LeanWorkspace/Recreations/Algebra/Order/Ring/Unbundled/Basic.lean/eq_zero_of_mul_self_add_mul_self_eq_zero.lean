import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem eq_zero_of_mul_self_add_mul_self_eq_zero [NoZeroDivisors R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    (h : a * a + b * b = 0) : a = 0 := (mul_self_add_mul_self_eq_zero.mp h).left

