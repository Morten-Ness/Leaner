import Mathlib

variable {R : Type*}

variable [Monoid R] {a b : R} {n : ℕ}

theorem isRightRegular_of_mul_eq_one (h : a * b = 1) : IsRightRegular a := IsRightRegular.of_mul (a := b) (by rw [h]; exact isRegular_one.right)

