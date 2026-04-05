import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_mul_column (v : n → R) (A : Matrix n n R) :
    Matrix.det (of fun i j => v i * A i j) = (∏ i, v i) * Matrix.det A := MultilinearMap.map_smul_univ _ v A

