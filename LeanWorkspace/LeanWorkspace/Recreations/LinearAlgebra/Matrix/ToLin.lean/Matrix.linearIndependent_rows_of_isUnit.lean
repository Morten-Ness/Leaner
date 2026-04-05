import Mathlib

variable {R : Type*} [Semiring R]

variable {l m n : Type*}

variable [Fintype m]

theorem Matrix.linearIndependent_rows_of_isUnit {A : Matrix m m R}
    [DecidableEq m] (ha : IsUnit A) : LinearIndependent R A.row := by
  rw [← Matrix.vecMul_injective_iff]
  exact Matrix.vecMul_injective_of_isUnit ha

