import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_zero (f : R[X]) : Polynomial.expand R 0 f = Polynomial.C (eval 1 f) := by simp [Polynomial.expand]

