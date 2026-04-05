import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem smul_eq_C_mul (a : R) : a • p = Polynomial.C a * p := by simp [ext_iff]

