import Mathlib

variable {α : Type*}

variable {K : Type*} [DivisionSemiring K] [PartialOrder K] [PosMulReflectLT K]
  [IsOrderedCancelAddMonoid K] [ExistsAddOfLE K] {a : K}

theorem image_affine_Ico (h : 0 < a) (b c d : K) :
    (a * · + b) '' Ico c d = Ico (a * c + b) (a * d + b) := by
  suffices (· + b) '' ((a * ·) '' Ico c d) = Ico (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [Set.image_mul_left_Ico h, image_add_const_Ico]

