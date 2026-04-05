import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

theorem bind₂_X_right (f : R →+* MvPolynomial σ S) (i : σ) : MvPolynomial.bind₂ f (X i) = X i := eval₂Hom_X' f X i

