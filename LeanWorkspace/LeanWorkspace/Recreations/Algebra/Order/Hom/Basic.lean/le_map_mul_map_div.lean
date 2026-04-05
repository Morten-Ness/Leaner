import Mathlib

variable {ι F α β γ δ : Type*}

variable [FunLike F α β]

theorem le_map_mul_map_div [Group α] [CommMagma β] [LE β] [SubmultiplicativeHomClass F α β]
    (f : F) (a b : α) : f a ≤ f b * f (a / b) := by
  simpa only [mul_comm, div_mul_cancel] using map_mul_le_mul f (a / b) b

