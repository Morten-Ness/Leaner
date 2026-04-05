import Mathlib

variable {R : Type*} [CommSemiring R]

theorem isHomogenous_toTupleMvPolynomial (p : R[X]) (i : Fin 2) :
    (p.toTupleMvPolynomial i).IsHomogeneous p.natDegree := by
  fin_cases i
  · simp [Polynomial.toTupleMvPolynomial]
  · simpa [Polynomial.toTupleMvPolynomial] using MvPolynomial.isHomogeneous_X_pow 1 p.natDegree

