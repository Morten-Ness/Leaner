import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

theorem aeval_eq_bind₁ (f : σ → MvPolynomial τ R) : aeval f = MvPolynomial.bind₁ f := rfl

