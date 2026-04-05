import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_mul_row (v : n → R) (A : Matrix n n R) :
    Matrix.det (of fun i j => v j * A i j) = (∏ i, v i) * Matrix.det A := calc
    Matrix.det (of fun i j => v j * A i j) = Matrix.det (A * diagonal v) :=
      congr_arg Matrix.det <| by
        ext
        simp [mul_comm]
    _ = (∏ i, v i) * Matrix.det A := by rw [Matrix.det_mul, Matrix.det_diagonal, mul_comm]

