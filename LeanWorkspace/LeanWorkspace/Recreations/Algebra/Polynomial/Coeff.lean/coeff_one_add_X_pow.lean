import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_one_add_X_pow (R : Type*) [Semiring R] (n k : ℕ) :
    ((1 + Polynomial.X) ^ n).coeff k = (n.choose k : R) := by rw [add_comm _ Polynomial.X, Polynomial.coeff_X_add_one_pow]

