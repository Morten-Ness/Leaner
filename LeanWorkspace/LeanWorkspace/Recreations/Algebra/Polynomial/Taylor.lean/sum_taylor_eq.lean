import Mathlib

variable {R : Type*} [CommRing R] (r : R) (f : R[X])

theorem sum_taylor_eq (f : R[X]) (r : R) :
    ((Polynomial.taylor r f).sum fun i a => C a * (X - C r) ^ i) = f := by
  rw [← comp_eq_sum_left, sub_eq_add_neg, ← C_neg, ← Polynomial.taylor_apply, Polynomial.taylor_taylor, neg_add_cancel,
    Polynomial.taylor_zero]

