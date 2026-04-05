import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_eq_C {p : ℕ} (hp : 0 < p) {f : R[X]} {r : R} : Polynomial.expand R p f = Polynomial.C r ↔ f = Polynomial.C r := by
  rw [← Polynomial.expand_C, Polynomial.expand_inj hp, Polynomial.expand_C]

