import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₁_monomial (f : σ → MvPolynomial τ R) (d : σ →₀ ℕ) (r : R) :
    MvPolynomial.bind₁ f (monomial d r) = C r * ∏ i ∈ d.support, f i ^ d i := by
  simp only [monomial_eq, map_mul, MvPolynomial.bind₁_C_right, Finsupp.prod, map_prod,
    map_pow, MvPolynomial.bind₁_X_right]

