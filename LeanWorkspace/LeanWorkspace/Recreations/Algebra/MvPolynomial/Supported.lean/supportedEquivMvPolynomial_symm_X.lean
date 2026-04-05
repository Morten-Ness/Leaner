import Mathlib

variable {σ : Type*} {R : Type u}

variable [CommSemiring R] {p : MvPolynomial σ R}

theorem supportedEquivMvPolynomial_symm_X (s : Set σ) (i : s) :
    (↑((MvPolynomial.supportedEquivMvPolynomial s).symm (X i : MvPolynomial s R)) : MvPolynomial σ R) =
      X ↑i := by
  simp [MvPolynomial.supportedEquivMvPolynomial]

