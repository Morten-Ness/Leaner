import Mathlib

open scoped Function -- required for scoped `on` notation Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

theorem coe_lt_degree {p : R[X]} {n : ℕ} : (n : WithBot ℕ) < degree p ↔ n < natDegree p := by
  by_cases h : p = 0
  · simp [h]
  simp [degree_eq_natDegree h, Nat.cast_lt]

