import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R]

theorem leadingCoeff_pow_X_add_C (r : R) (i : ℕ) : leadingCoeff ((Polynomial.X + Polynomial.C r) ^ i) = 1 := by
  nontriviality
  rw [Polynomial.leadingCoeff_pow'] <;> simp

