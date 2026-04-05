import Mathlib

variable (R : Type*) [Ring R] {S : Type*} [AddCommGroup S] [Pow S ℕ] [Module R S] (p q : R[X])
  (x : S)

theorem smeval_sub : (p - q).smeval x = p.smeval x - q.smeval x := by
  rw [sub_eq_add_neg, Polynomial.smeval_add, Polynomial.smeval_neg, sub_eq_add_neg]

