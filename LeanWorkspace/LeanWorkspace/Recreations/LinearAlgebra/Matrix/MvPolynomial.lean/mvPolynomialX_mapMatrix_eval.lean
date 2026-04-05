import Mathlib

variable {m n R S : Type*}

theorem mvPolynomialX_mapMatrix_eval [Fintype m] [DecidableEq m] [CommSemiring R]
    (A : Matrix m m R) :
    (MvPolynomial.eval fun p : m × m => A p.1 p.2).mapMatrix (Matrix.mvPolynomialX m m R) = A := Matrix.mvPolynomialX_map_eval₂ _ A

