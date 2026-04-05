import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem join₁_rename (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    MvPolynomial.join₁ (rename f φ) = MvPolynomial.bind₁ f φ := MvPolynomial.aeval_id_rename _ _

