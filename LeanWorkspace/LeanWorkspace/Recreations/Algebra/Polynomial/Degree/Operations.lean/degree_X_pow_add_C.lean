import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Nontrivial R]

variable [Semiring R]

theorem degree_X_pow_add_C {n : ℕ} (hn : 0 < n) (a : R) : degree ((Polynomial.X : R[X]) ^ n + Polynomial.C a) = n := by
  have : degree (Polynomial.C a) < degree ((Polynomial.X : R[X]) ^ n) := degree_C_le.trans_lt <| by
    rwa [degree_X_pow, Nat.cast_pos]
  rw [Polynomial.degree_add_eq_left_of_degree_lt this, degree_X_pow]

