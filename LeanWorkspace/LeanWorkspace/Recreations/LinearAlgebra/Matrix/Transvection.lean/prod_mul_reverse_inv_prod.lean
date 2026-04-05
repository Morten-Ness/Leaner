import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

variable [Fintype n]

theorem prod_mul_reverse_inv_prod (L : List (Matrix.TransvectionStruct n R)) :
    (L.map Matrix.TransvectionStruct.toMatrix).prod * (L.reverse.map (Matrix.TransvectionStruct.toMatrix ∘ Matrix.TransvectionStruct.inv)).prod = 1 := by
  induction L with
  | nil => simp
  | cons t L IH =>
    suffices
      t.toMatrix *
            ((L.map Matrix.TransvectionStruct.toMatrix).prod * (L.reverse.map (Matrix.TransvectionStruct.toMatrix ∘ Matrix.TransvectionStruct.inv)).prod) *
          t.inv.toMatrix = 1
      by simpa [Matrix.mul_assoc]
    simp_rw [IH, Matrix.mul_one, Matrix.TransvectionStruct.mul_inv t]

