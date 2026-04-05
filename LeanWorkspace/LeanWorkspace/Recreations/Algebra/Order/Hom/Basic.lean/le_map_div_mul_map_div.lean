import Mathlib

variable {ι F α β γ δ : Type*}

variable [FunLike F α β]

theorem le_map_div_mul_map_div [Group α] [Mul β] [LE β] [SubmultiplicativeHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) * f (b / c) := by
  simpa only [div_mul_div_cancel] using map_mul_le_mul f (a / b) (b / c)

