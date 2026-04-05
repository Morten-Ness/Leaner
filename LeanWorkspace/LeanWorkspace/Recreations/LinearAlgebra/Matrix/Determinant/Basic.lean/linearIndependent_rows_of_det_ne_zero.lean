import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem linearIndependent_rows_of_det_ne_zero [IsDomain R] {A : Matrix m m R} (hA : A.det ≠ 0) :
    LinearIndependent R (fun i ↦ A i) := by
  contrapose! hA
  exact Matrix.det_eq_zero_of_not_linearIndependent_rows hA

