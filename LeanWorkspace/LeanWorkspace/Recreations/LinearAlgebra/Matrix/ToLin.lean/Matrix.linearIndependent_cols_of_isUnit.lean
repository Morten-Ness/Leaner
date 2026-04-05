import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*}

variable [Fintype n]

theorem Matrix.linearIndependent_cols_of_isUnit [Fintype m]
    {A : Matrix m m R} [DecidableEq m] (ha : IsUnit A) :
    LinearIndependent R A.col := by
  rw [← Matrix.mulVec_injective_iff]
  exact Matrix.mulVec_injective_of_isUnit ha

