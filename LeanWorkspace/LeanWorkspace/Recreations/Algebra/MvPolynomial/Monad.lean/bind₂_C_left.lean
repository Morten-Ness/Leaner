import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₂_C_left : MvPolynomial.bind₂ (C : R →+* MvPolynomial σ R) = RingHom.id _ := by ext : 2 <;> simp

