import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

theorem transvection_zero : Matrix.transvection i j (0 : R) = 1 := by simp [Matrix.transvection]

