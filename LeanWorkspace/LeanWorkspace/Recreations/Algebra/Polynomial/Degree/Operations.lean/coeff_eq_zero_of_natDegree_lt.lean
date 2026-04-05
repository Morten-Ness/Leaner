import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem coeff_eq_zero_of_natDegree_lt {p : R[X]} {n : ℕ} (h : p.natDegree < n) :
    p.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_degree_lt
  by_cases hp : p = 0
  · subst hp
    exact WithBot.bot_lt_coe n
  · rwa [degree_eq_natDegree hp, Nat.cast_lt]

