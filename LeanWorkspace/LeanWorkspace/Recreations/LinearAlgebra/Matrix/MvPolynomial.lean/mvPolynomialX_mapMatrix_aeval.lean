import Mathlib

variable {m n R S : Type*}

theorem mvPolynomialX_mapMatrix_aeval [Fintype m] [DecidableEq m] [CommSemiring R] [CommSemiring S]
    [Algebra R S] (A : Matrix m m S) :
    (MvPolynomial.aeval fun p : m × m => A p.1 p.2).mapMatrix (Matrix.mvPolynomialX m m R) = A := Matrix.mvPolynomialX_map_eval₂ _ A

