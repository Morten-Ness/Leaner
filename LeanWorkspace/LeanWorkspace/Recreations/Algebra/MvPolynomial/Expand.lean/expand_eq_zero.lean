import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_eq_zero {p : ℕ} (hp : 0 < p) {f : MvPolynomial σ R} : MvPolynomial.expand p f = 0 ↔ f = 0 := (MvPolynomial.expand_injective hp).eq_iff' (map_zero _)

