import Mathlib

variable {R : Type*} [CommSemiring R]

theorem toTupleMvPolynomial_zero_eq (p : R[X]) :
    p.toTupleMvPolynomial 0 = p.homogenize p.natDegree := rfl

