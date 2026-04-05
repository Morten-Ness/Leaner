import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_X_of_ne_one {n : ℕ} (hn : n ≠ 1) : Polynomial.coeff (Polynomial.X : R[X]) n = 0 := by
  rw [Polynomial.coeff_X, if_neg hn.symm]

