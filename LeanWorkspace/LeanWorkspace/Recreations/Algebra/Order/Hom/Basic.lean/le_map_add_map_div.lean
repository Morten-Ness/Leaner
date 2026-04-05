import Mathlib

variable {ι F α β γ δ : Type*}

variable [FunLike F α β]

theorem le_map_add_map_div [Group α] [AddCommMagma β] [LE β] [MulLEAddHomClass F α β] (f : F)
    (a b : α) : f a ≤ f b + f (a / b) := by
  simpa only [add_comm, div_mul_cancel] using map_mul_le_add f (a / b) b

