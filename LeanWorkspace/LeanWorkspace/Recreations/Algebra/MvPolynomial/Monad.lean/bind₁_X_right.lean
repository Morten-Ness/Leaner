import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

theorem bind₁_X_right (f : σ → MvPolynomial τ R) (i : σ) : MvPolynomial.bind₁ f (X i) = f i := aeval_X f i

