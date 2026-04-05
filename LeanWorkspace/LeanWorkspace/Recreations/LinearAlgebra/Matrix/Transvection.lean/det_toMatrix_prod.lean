import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

theorem det_toMatrix_prod [Fintype n] (L : List (Matrix.TransvectionStruct n R)) :
    Matrix.TransvectionStruct.det (L.map Matrix.TransvectionStruct.toMatrix).prod = 1 := by
  induction L with
  | nil => simp
  | cons _ _ IH => simp [IH]

