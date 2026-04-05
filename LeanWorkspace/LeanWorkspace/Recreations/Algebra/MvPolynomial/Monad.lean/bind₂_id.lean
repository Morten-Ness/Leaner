import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₂_id : MvPolynomial.bind₂ (RingHom.id (MvPolynomial σ R)) = MvPolynomial.join₂ := rfl

