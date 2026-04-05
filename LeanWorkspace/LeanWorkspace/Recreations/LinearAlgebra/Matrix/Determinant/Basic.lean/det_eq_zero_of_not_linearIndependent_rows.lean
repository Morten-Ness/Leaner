import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_eq_zero_of_not_linearIndependent_rows [IsDomain R] {A : Matrix m m R}
    (hA : ¬ LinearIndependent R (fun i ↦ A i)) :
    Matrix.det A = 0 := Matrix.detRowAlternating.map_linearDependent A hA

