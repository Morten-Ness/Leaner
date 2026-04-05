import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem rename_comp_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → υ) :
    (rename g).comp (MvPolynomial.bind₁ f) = MvPolynomial.bind₁ fun i => rename g <| f i := by
  ext1 i
  simp

