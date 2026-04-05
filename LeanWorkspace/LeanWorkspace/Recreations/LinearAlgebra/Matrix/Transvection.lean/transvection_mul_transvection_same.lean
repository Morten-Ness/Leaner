import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

variable [Fintype n]

theorem transvection_mul_transvection_same (h : i ≠ j) (c d : R) :
    Matrix.transvection i j c * Matrix.transvection i j d = Matrix.transvection i j (c + d) := by
  simp [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, h.symm, add_assoc,
    single_add]

