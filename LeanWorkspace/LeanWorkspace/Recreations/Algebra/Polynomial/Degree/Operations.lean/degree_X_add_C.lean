import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Nontrivial R]

variable [Semiring R]

theorem degree_X_add_C (a : R) : degree (Polynomial.X + Polynomial.C a) = 1 := by
  have : degree (Polynomial.C a) < degree (Polynomial.X : R[X]) :=
    calc
      degree (Polynomial.C a) ≤ 0 := degree_C_le
      _ < 1 := WithBot.coe_lt_coe.mpr zero_lt_one
      _ = degree Polynomial.X := degree_X.symm
  rw [Polynomial.degree_add_eq_left_of_degree_lt this, degree_X]

