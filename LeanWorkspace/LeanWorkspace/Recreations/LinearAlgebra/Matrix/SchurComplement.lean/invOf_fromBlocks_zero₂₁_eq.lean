import Mathlib

open scoped Matrix

variable {l m n α : Type*}

variable [Fintype l] [Fintype m] [Fintype n]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [CommRing α]

theorem invOf_fromBlocks_zero₂₁_eq (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α)
    [Invertible A] [Invertible D] [Invertible (fromBlocks A B 0 D)] :
    ⅟(fromBlocks A B 0 D) = fromBlocks (⅟A) (-(⅟A * B * ⅟D)) 0 (⅟D) := by
  letI := Matrix.fromBlocksZero₂₁Invertible A B D
  convert (rfl : ⅟(fromBlocks A B 0 D) = _)

