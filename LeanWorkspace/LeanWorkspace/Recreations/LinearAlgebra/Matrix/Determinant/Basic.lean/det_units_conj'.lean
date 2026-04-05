import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    Matrix.det (M⁻¹.val * N * ↑M.val) = Matrix.det N := Matrix.det_units_conj M⁻¹ N

