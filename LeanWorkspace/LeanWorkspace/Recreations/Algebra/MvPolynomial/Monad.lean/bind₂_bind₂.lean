import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₂_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* MvPolynomial σ T)
    (φ : MvPolynomial σ R) : (MvPolynomial.bind₂ g) (MvPolynomial.bind₂ f φ) = MvPolynomial.bind₂ ((MvPolynomial.bind₂ g).comp f) φ := RingHom.congr_fun (MvPolynomial.bind₂_comp_bind₂ f g) φ

