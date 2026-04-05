import Mathlib

variable {α : Type*}

variable {K : Type*} [DivisionSemiring K] [PartialOrder K] [PosMulReflectLT K]
  [IsOrderedCancelAddMonoid K] [ExistsAddOfLE K] {a : K}

theorem image_affine_Icc' (h : 0 < a) (b c d : K) :
    (a * · + b) '' Icc c d = Icc (a * c + b) (a * d + b) := by
  suffices (· + b) '' ((a * ·) '' Icc c d) = Icc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [Set.image_mul_left_Icc' h, image_add_const_Icc]

