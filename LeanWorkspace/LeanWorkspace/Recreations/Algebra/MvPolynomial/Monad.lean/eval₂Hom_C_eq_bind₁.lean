import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

theorem eval₂Hom_C_eq_bind₁ (f : σ → MvPolynomial τ R) : eval₂Hom C f = MvPolynomial.bind₁ f := rfl

