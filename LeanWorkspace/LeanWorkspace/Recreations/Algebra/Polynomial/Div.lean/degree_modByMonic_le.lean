import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem degree_modByMonic_le (p : R[X]) {q : R[X]} (hq : Polynomial.Monic q) : degree (p %ₘ q) ≤ degree q := by
  nontriviality R
  exact (Polynomial.degree_modByMonic_lt _ hq).le

