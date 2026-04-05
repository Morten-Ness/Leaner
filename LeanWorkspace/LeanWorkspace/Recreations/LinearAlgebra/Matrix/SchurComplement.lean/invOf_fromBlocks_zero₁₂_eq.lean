import Mathlib

open scoped Matrix

variable {l m n α : Type*}

variable [Fintype l] [Fintype m] [Fintype n]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [CommRing α]

theorem invOf_fromBlocks_zero₁₂_eq (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible A] [Invertible D] [Invertible (fromBlocks A 0 C D)] :
    ⅟(fromBlocks A 0 C D) = fromBlocks (⅟A) 0 (-(⅟D * C * ⅟A)) (⅟D) := by
  letI := Matrix.fromBlocksZero₁₂Invertible A C D
  convert (rfl : ⅟(fromBlocks A 0 C D) = _)

