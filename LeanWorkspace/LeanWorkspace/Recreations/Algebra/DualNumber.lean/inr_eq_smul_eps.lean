import Mathlib

variable {R A B : Type*}

theorem inr_eq_smul_eps [MulZeroOneClass R] (r : R) : inr r = (r • ε : R[ε]) := ext (mul_zero r).symm (mul_one r).symm

