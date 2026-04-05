import Mathlib

variable {σ : Type*} {R : Type u}

variable [CommSemiring R] {p : MvPolynomial σ R}

theorem supportedEquivMvPolynomial_symm_C (s : Set σ) (x : R) :
    (MvPolynomial.supportedEquivMvPolynomial s).symm (C x) = algebraMap R (MvPolynomial.supported R s) x := by
  ext1
  simp [MvPolynomial.supportedEquivMvPolynomial, MvPolynomial.algebraMap_eq]

