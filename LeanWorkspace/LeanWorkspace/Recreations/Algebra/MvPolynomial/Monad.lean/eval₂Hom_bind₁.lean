import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem eval₂Hom_bind₁ (f : R →+* S) (g : τ → S) (h : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    eval₂Hom f g (MvPolynomial.bind₁ h φ) = eval₂Hom f (fun i => eval₂Hom f g (h i)) φ := by
  rw [MvPolynomial.hom_bind₁, MvPolynomial.eval₂Hom_comp_C]

