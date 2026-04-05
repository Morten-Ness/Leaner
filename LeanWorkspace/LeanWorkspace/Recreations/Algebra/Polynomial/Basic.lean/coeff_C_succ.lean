import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_C_succ {r : R} {n : ℕ} : Polynomial.coeff (Polynomial.C r) (n + 1) = 0 := by simp [Polynomial.coeff_C]

