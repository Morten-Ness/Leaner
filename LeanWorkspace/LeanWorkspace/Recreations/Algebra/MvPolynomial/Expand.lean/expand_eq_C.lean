import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_eq_C {p : ℕ} (hp : 0 < p) {f : MvPolynomial σ R} {r : R} :
    MvPolynomial.expand p f = C r ↔ f = C r := by
  rw [← MvPolynomial.expand_C, MvPolynomial.expand_inj hp, MvPolynomial.expand_C]

