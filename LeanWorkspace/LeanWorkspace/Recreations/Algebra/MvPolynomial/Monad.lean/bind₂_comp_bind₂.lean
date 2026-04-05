import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₂_comp_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* MvPolynomial σ T) :
    (MvPolynomial.bind₂ g).comp (MvPolynomial.bind₂ f) = MvPolynomial.bind₂ ((MvPolynomial.bind₂ g).comp f) := by ext : 2 <;> simp

