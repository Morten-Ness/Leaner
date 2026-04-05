import Mathlib

variable {α : Type*}

variable {K : Type*} [DivisionSemiring K] [PartialOrder K] [PosMulReflectLT K]
  [IsOrderedCancelAddMonoid K] [ExistsAddOfLE K] {a : K}

theorem image_affine_Ioo (h : 0 < a) (b c d : K) :
    (a * · + b) '' Ioo c d = Ioo (a * c + b) (a * d + b) := by
  suffices (· + b) '' ((a * ·) '' Ioo c d) = Ioo (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [Set.image_mul_left_Ioo h, image_add_const_Ioo]

