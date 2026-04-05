import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₁_C_right (f : σ → MvPolynomial τ R) (x) : MvPolynomial.bind₁ f (C x) = C x := algHom_C _ _

