import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_inj {p : ℕ} (hp : 0 < p) {f g : R[X]} : Polynomial.expand R p f = Polynomial.expand R p g ↔ f = g := (Polynomial.expand_injective hp).eq_iff

