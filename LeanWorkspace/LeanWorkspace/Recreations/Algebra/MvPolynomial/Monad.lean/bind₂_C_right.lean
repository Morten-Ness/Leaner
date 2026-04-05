import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₂_C_right (f : R →+* MvPolynomial σ S) (r : R) : MvPolynomial.bind₂ f (C r) = f r := eval₂Hom_C f X r

