import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_eq_zero_of_not_linearIndependent_cols [IsDomain R] {A : Matrix m m R}
    (hA : ¬ LinearIndependent R (fun i ↦ Aᵀ i)) :
    Matrix.det A = 0 := by
  contrapose! hA
  exact Matrix.linearIndependent_cols_of_det_ne_zero hA

