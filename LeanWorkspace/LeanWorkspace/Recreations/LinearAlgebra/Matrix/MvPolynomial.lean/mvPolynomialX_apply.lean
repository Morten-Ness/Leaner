import Mathlib

variable {m n R S : Type*}

theorem mvPolynomialX_apply [CommSemiring R] (i j) :
    Matrix.mvPolynomialX m n R i j = MvPolynomial.X (i, j) := rfl

