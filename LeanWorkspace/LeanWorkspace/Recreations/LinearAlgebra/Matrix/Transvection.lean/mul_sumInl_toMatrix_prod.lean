import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

theorem mul_sumInl_toMatrix_prod [Fintype n] [Fintype p] (M : Matrix n n R)
    (L : List (Matrix.TransvectionStruct n R)) (N : Matrix p p R) :
    fromBlocks M 0 0 N * (L.map (Matrix.TransvectionStruct.toMatrix ∘ Matrix.TransvectionStruct.sumInl p)).prod =
      fromBlocks (M * (L.map Matrix.TransvectionStruct.toMatrix).prod) 0 0 N := by
  induction L generalizing M N with
  | nil => simp
  | cons t L IH => simp [IH, Matrix.TransvectionStruct.toMatrix_sumInl, fromBlocks_multiply]

