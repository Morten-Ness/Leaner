import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₂_comp_C (f : R →+* MvPolynomial σ S) : (MvPolynomial.bind₂ f).comp C = f := RingHom.ext <| MvPolynomial.bind₂_C_right _

