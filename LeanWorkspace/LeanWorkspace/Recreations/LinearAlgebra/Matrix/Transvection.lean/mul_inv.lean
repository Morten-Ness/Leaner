import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

variable [Fintype n]

theorem mul_inv (t : Matrix.TransvectionStruct n R) : t.toMatrix * t.inv.toMatrix = 1 := by
  rcases t with ⟨_, _, t_hij⟩
  simp [Matrix.TransvectionStruct.toMatrix, Matrix.transvection_mul_transvection_same, t_hij]

