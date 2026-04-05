import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

theorem toMatrix_sumInl (t : Matrix.TransvectionStruct n R) :
    (t.sumInl p).toMatrix = fromBlocks t.toMatrix 0 0 1 := by
  cases t
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · by_cases h : a = b <;> simp [Matrix.TransvectionStruct.sumInl, Matrix.transvection, h, single]
  · simp [Matrix.TransvectionStruct.sumInl, Matrix.transvection]
  · simp [Matrix.TransvectionStruct.sumInl, Matrix.transvection]
  · by_cases h : a = b <;> simp [Matrix.TransvectionStruct.sumInl, Matrix.transvection, h]

