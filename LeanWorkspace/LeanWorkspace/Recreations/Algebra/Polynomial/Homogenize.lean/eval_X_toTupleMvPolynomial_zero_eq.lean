import Mathlib

variable {R : Type*} [CommSemiring R]

theorem eval_X_toTupleMvPolynomial_zero_eq (p : R[X]) :
    MvPolynomial.aeval ![X, 1] (p.toTupleMvPolynomial 0) =
      p * MvPolynomial.aeval ![X, 1] (p.toTupleMvPolynomial 1) := by
  simp [Polynomial.toTupleMvPolynomial]

