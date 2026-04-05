import Mathlib

variable {R : Type*}

variable [Monoid R] {a b : R} {n : ℕ}

theorem isLeftRegular_of_mul_eq_one (h : b * a = 1) : IsLeftRegular a := IsLeftRegular.of_mul (a := b) (by rw [h]; exact isRegular_one.left)

