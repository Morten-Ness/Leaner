import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem aeval_bind₂ [Algebra S T] (f : σ → T) (g : R →+* MvPolynomial σ S) (φ : MvPolynomial σ R) :
    aeval f (MvPolynomial.bind₂ g φ) = eval₂Hom ((↑(aeval f : _ →ₐ[S] _) : _ →+* _).comp g) f φ := MvPolynomial.eval₂Hom_bind₂ _ _ _ _

alias eval₂Hom_C_left := MvPolynomial.eval₂Hom_C_eq_bind₁

