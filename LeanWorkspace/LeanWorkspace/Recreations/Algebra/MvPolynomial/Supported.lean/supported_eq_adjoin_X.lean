import Mathlib

variable {σ : Type*} {R : Type u}

variable [CommSemiring R] {p : MvPolynomial σ R}

variable {s t : Set σ}

theorem supported_eq_adjoin_X : MvPolynomial.supported R s = Algebra.adjoin R (X '' s) := rfl

