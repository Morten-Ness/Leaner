import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_ne_zero {p : ℕ} (hp : 0 < p) {f : R[X]} : Polynomial.expand R p f ≠ 0 ↔ f ≠ 0 := (Polynomial.expand_eq_zero hp).not

