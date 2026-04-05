import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₁_comp_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R) :
    (MvPolynomial.bind₁ g).comp (MvPolynomial.bind₁ f) = MvPolynomial.bind₁ fun i => MvPolynomial.bind₁ g (f i) := by
  ext1
  apply MvPolynomial.bind₁_bind₁

