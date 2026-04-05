import Mathlib

variable {R : Type*} [CommSemiring R]

theorem toTupleMvPolynomial_one_eq (p : R[X]) :
    p.toTupleMvPolynomial 1 = (MvPolynomial.X 1) ^ p.natDegree := rfl

