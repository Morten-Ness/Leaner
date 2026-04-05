import Mathlib

open scoped Matrix

variable {l m n α : Type*}

variable [Fintype l] [Fintype m] [Fintype n]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [CommRing α]

theorem invOf_fromBlocks₁₁_eq (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] [Invertible (D - C * ⅟A * B)]
    [Invertible (fromBlocks A B C D)] :
    ⅟(fromBlocks A B C D) =
      fromBlocks (⅟A + ⅟A * B * ⅟(D - C * ⅟A * B) * C * ⅟A) (-(⅟A * B * ⅟(D - C * ⅟A * B)))
        (-(⅟(D - C * ⅟A * B) * C * ⅟A)) (⅟(D - C * ⅟A * B)) := by
  letI := Matrix.fromBlocks₁₁Invertible A B C D
  convert (rfl : ⅟(fromBlocks A B C D) = _)

