import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₁_id : MvPolynomial.bind₁ (@id (MvPolynomial σ R)) = MvPolynomial.join₁ := rfl

