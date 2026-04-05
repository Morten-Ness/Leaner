import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_mul_X_pow' (p : R[X]) (n d : ℕ) :
    (p * Polynomial.X ^ n).coeff d = ite (n ≤ d) (p.coeff (d - n)) 0 := by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, Polynomial.coeff_mul_X_pow, add_tsub_cancel_right]
  · refine (Polynomial.coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [Polynomial.coeff_X_pow, if_neg, mul_zero]
    exact ((le_of_add_le_right (mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h).ne

