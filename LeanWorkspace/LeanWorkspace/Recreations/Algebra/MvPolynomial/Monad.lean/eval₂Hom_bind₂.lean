import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem eval₂Hom_bind₂ (f : S →+* T) (g : σ → T) (h : R →+* MvPolynomial σ S)
    (φ : MvPolynomial σ R) : eval₂Hom f g (MvPolynomial.bind₂ h φ) = eval₂Hom ((eval₂Hom f g).comp h) g φ := RingHom.congr_fun (MvPolynomial.eval₂Hom_comp_bind₂ f g h) φ

