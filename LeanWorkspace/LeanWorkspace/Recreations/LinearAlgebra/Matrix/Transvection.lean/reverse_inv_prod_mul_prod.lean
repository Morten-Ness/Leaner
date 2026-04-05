import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

variable [Fintype n]

theorem reverse_inv_prod_mul_prod (L : List (Matrix.TransvectionStruct n R)) :
    (L.reverse.map (Matrix.TransvectionStruct.toMatrix ∘ Matrix.TransvectionStruct.inv)).prod * (L.map Matrix.TransvectionStruct.toMatrix).prod = 1 := by
  induction L with
  | nil => simp
  | cons t L IH =>
    suffices
      (L.reverse.map (Matrix.TransvectionStruct.toMatrix ∘ Matrix.TransvectionStruct.inv)).prod * (t.inv.toMatrix * t.toMatrix) *
          (L.map Matrix.TransvectionStruct.toMatrix).prod = 1
      by simpa [Matrix.mul_assoc]
    simpa [Matrix.TransvectionStruct.inv_mul] using IH

