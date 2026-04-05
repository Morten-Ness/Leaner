import Mathlib

variable {R : Type*}

variable [Monoid R] {a b : R} {n : ℕ}

theorem Units.isRegular (a : Rˣ) : IsRegular (a : R) := ⟨isLeftRegular_of_mul_eq_one a.inv_mul, isRightRegular_of_mul_eq_one a.mul_inv⟩

