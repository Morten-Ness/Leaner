import Mathlib

variable {R : Type*}

variable [Monoid R] {a b : R} {n : ℕ}

theorem IsRightRegular.pow (n : ℕ) (rra : IsRightRegular a) : IsRightRegular (a ^ n) := by
  rw [IsRightRegular, ← mul_right_iterate]
  exact rra.iterate n

