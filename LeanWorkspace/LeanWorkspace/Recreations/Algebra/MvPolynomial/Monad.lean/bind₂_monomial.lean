import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₂_monomial (f : R →+* MvPolynomial σ S) (d : σ →₀ ℕ) (r : R) :
    MvPolynomial.bind₂ f (monomial d r) = f r * monomial d 1 := by
  simp only [monomial_eq, map_mul, MvPolynomial.bind₂_C_right, Finsupp.prod, map_prod,
    map_pow, MvPolynomial.bind₂_X_right, C_1, one_mul]

