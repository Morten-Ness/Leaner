import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem aeval_comp_bind₁ [Algebra R S] (f : τ → S) (g : σ → MvPolynomial τ R) :
    (aeval f).comp (MvPolynomial.bind₁ g) = aeval fun i => aeval f (g i) := by
  ext1
  apply MvPolynomial.aeval_bind₁

