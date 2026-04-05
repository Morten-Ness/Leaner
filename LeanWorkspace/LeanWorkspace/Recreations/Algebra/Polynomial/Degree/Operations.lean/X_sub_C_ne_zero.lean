import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

variable [Nontrivial R]

theorem X_sub_C_ne_zero (r : R) : Polynomial.X - Polynomial.C r ≠ 0 := pow_one (Polynomial.X : R[X]) ▸ Polynomial.X_pow_sub_C_ne_zero zero_lt_one r

