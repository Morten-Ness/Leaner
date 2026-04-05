import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

variable [Fintype n]

theorem transvection_mul_apply_same (b : n) (c : R) (M : Matrix n n R) :
    (Matrix.transvection i j c * M) i b = M i b + c * M j b := by simp [Matrix.transvection, Matrix.add_mul]

