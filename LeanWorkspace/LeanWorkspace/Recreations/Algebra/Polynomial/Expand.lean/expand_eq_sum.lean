import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_eq_sum {f : R[X]} : Polynomial.expand R p f = f.sum fun e a => Polynomial.C a * (Polynomial.X ^ p) ^ e := by
  simp [Polynomial.expand, eval₂]

