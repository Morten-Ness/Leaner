import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_C (a : R) : Polynomial.natDegree (Polynomial.C a) = 0 := by
  by_cases ha : a = 0
  · have : Polynomial.C a = 0 := by rw [ha, C_0]
    rw [Polynomial.natDegree, Polynomial.degree_eq_bot.2 this, WithBot.unbotD_bot]
  · rw [Polynomial.natDegree, Polynomial.degree_C ha, WithBot.unbotD_zero]

