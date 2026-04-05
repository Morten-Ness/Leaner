import Mathlib

variable (R : Type*) [Ring R] {S : Type*} [AddCommGroup S] [Pow S ℕ] [Module R S] (p q : R[X])
  (x : S)

theorem smeval_neg : (-p).smeval x = -p.smeval x := by
  rw [← add_eq_zero_iff_eq_neg, ← Polynomial.smeval_add, neg_add_cancel, Polynomial.smeval_zero]

