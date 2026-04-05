import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem monic_X_pow_add {n : ℕ} (H : degree p < n) : Polynomial.Monic (Polynomial.X ^ n + p) := monic_of_degree_le n
    (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H)))
    (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H, add_zero])

