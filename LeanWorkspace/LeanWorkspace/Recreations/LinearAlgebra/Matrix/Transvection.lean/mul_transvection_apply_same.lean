import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

variable [Fintype n]

theorem mul_transvection_apply_same (a : n) (c : R) (M : Matrix n n R) :
    (M * Matrix.transvection i j c) a j = M a j + c * M a i := by
  simp [Matrix.transvection, Matrix.mul_add, mul_comm]

