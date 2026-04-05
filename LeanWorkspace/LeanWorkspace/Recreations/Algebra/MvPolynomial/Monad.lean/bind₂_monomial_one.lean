import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₂_monomial_one (f : R →+* MvPolynomial σ S) (d : σ →₀ ℕ) :
    MvPolynomial.bind₂ f (monomial d 1) = monomial d 1 := by rw [MvPolynomial.bind₂_monomial, f.map_one, one_mul]

