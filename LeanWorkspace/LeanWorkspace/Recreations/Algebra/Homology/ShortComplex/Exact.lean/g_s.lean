import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem g_s (s : S.Splitting) : S.g ≫ s.s = 𝟙 _ - s.r ≫ S.f := by rw [← s.id, add_sub_cancel_left]

