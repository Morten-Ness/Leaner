import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R]

theorem leadingCoeff_X_pow_add_one {n : ℕ} (hn : 0 < n) : (Polynomial.X ^ n + 1 : R[X]).leadingCoeff = 1 := Polynomial.leadingCoeff_X_pow_add_C hn

