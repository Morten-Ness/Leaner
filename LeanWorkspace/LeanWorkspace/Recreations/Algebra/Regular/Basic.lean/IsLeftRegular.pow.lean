import Mathlib

variable {R : Type*}

variable [Monoid R] {a b : R} {n : ℕ}

theorem IsLeftRegular.pow (n : ℕ) (rla : IsLeftRegular a) : IsLeftRegular (a ^ n) := by
  simp only [IsLeftRegular, ← mul_left_iterate, rla.iterate n]

