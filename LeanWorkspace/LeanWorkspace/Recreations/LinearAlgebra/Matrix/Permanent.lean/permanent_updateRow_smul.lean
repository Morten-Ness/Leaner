import Mathlib

variable {n : Type*} [DecidableEq n] [Fintype n]

variable {R : Type*} [CommSemiring R]

theorem permanent_updateRow_smul (M : Matrix n n R) (j : n) (c : R) (u : n → R) :
    Matrix.permanent (updateRow M j <| c • u) = c * Matrix.permanent (updateRow M j u) := by
  rw [← Matrix.permanent_transpose, ← updateCol_transpose, Matrix.permanent_updateCol_smul,
    updateCol_transpose, Matrix.permanent_transpose]

