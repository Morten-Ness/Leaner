import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [DecidableEq m] {R K : Type*} [CommRing R] [Field K] [Fintype m]

theorem vecMul_surjective_iff_isUnit {A : Matrix m m R} :
    Function.Surjective A.vecMul ↔ IsUnit A := by
  rw [Matrix.vecMul_surjective_iff_exists_left_inverse, isUnit_iff_exists_inv']

