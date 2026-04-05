import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_reindex_self (e : m ≃ n) (A : Matrix m m R) : Matrix.det (reindex e e A) = Matrix.det A := Matrix.det_submatrix_equiv_self e.symm A

