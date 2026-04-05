import Mathlib

variable {σ : Type*} {R : Type u}

variable [CommSemiring R] {p : MvPolynomial σ R}

variable {s t : Set σ}

theorem supported_empty : MvPolynomial.supported R (∅ : Set σ) = ⊥ := by simp [MvPolynomial.supported_eq_adjoin_X]

