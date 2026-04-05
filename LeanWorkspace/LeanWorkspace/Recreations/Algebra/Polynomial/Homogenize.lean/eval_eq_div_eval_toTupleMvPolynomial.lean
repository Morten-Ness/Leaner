import Mathlib

variable {R : Type*} [CommSemiring R]

theorem eval_eq_div_eval_toTupleMvPolynomial {R : Type*} [Field R] (p : R[X]) (x : R) :
    p.eval x =
      (p.toTupleMvPolynomial 0).eval ![x, 1] / (p.toTupleMvPolynomial 1).eval ![x, 1] := by
  simp [Polynomial.toTupleMvPolynomial, Polynomial.eval_homogenize]

