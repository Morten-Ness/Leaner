import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R] {p q : R[X]}

theorem degree_X_sub_C_le (r : R) : (Polynomial.X - Polynomial.C r).degree ≤ 1 := (Polynomial.degree_sub_le _ _).trans (max_le Polynomial.degree_X_le (Polynomial.degree_C_le.trans zero_le_one))

