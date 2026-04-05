import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_X_add_one_pow (R : Type*) [Semiring R] (n k : ℕ) :
    ((Polynomial.X + 1) ^ n).coeff k = (n.choose k : R) := by rw [← C_1, Polynomial.coeff_X_add_C_pow, one_pow, one_mul]

