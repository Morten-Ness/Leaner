import Mathlib

open scoped Polynomial

variable {R : Type*} [Ring R]

theorem reflect_sub (f g : R[X]) (N : ℕ) : Polynomial.reflect N (f - g) = Polynomial.reflect N f - Polynomial.reflect N g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Polynomial.reflect_add, Polynomial.reflect_neg]

