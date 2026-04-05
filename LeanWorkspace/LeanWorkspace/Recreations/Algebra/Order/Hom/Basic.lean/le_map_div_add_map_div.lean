import Mathlib

variable {ι F α β γ δ : Type*}

variable [FunLike F α β]

theorem le_map_div_add_map_div [Group α] [Add β] [LE β] [MulLEAddHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) + f (b / c) := by
    simpa only [div_mul_div_cancel] using map_mul_le_add f (a / b) (b / c)

