import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natCast_comp {n : ℕ} : (n : R[X]).comp p = n := by rw [← C_eq_natCast, Polynomial.C_comp]

