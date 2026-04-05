import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem join₂_comp_map (f : R →+* MvPolynomial σ S) : MvPolynomial.join₂.comp (map f) = MvPolynomial.bind₂ f := RingHom.ext <| MvPolynomial.join₂_map _

