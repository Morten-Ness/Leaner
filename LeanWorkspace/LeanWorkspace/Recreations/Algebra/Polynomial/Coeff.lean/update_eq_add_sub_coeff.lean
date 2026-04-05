import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem update_eq_add_sub_coeff {R : Type*} [Ring R] (p : R[X]) (n : ℕ) (a : R) :
    p.update n a = p + Polynomial.C (a - p.coeff n) * Polynomial.X ^ n := by
  ext
  rw [coeff_update_apply, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  split_ifs with h <;> simp [h]

