import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Nontrivial R]

variable [Semiring R]

theorem X_add_C_ne_one (r : R) : Polynomial.X + Polynomial.C r ≠ 1 := pow_one (Polynomial.X : R[X]) ▸ Polynomial.X_pow_add_C_ne_one zero_lt_one r

