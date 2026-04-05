import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Ring R] {p : R[X]}

theorem monic_X_sub_C (x : R) : Polynomial.Monic (Polynomial.X - Polynomial.C x) := by
  simpa only [sub_eq_add_neg, C_neg] using Polynomial.monic_X_add_C (-x)

