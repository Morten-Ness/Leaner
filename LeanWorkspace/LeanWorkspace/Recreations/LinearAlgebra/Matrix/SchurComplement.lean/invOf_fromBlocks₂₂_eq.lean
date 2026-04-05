import Mathlib

open scoped Matrix

variable {l m n α : Type*}

variable [Fintype l] [Fintype m] [Fintype n]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [CommRing α]

theorem invOf_fromBlocks₂₂_eq (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible D] [Invertible (A - B * ⅟D * C)]
    [Invertible (fromBlocks A B C D)] :
    ⅟(fromBlocks A B C D) =
      fromBlocks (⅟(A - B * ⅟D * C)) (-(⅟(A - B * ⅟D * C) * B * ⅟D))
        (-(⅟D * C * ⅟(A - B * ⅟D * C))) (⅟D + ⅟D * C * ⅟(A - B * ⅟D * C) * B * ⅟D) := by
  letI := Matrix.fromBlocks₂₂Invertible A B C D
  convert (rfl : ⅟(fromBlocks A B C D) = _)

