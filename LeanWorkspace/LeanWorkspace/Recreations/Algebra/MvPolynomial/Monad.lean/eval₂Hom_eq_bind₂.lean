import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

theorem eval₂Hom_eq_bind₂ (f : R →+* MvPolynomial σ S) : eval₂Hom f X = MvPolynomial.bind₂ f := rfl

