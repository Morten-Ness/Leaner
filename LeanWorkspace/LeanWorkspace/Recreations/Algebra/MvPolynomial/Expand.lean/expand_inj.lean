import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_inj {p : ℕ} (hp : 0 < p) {f g : MvPolynomial σ R} :
    MvPolynomial.expand p f = MvPolynomial.expand p g ↔ f = g := (MvPolynomial.expand_injective hp).eq_iff

