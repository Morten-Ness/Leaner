import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

variable [Ring α]

theorem map_neg_one {F : Type*} [Ring β] [FunLike F α β] [RingHomClass F α β]
    (f : F) : map (f : α →* β) (-1) = -1 := by
  simp only [Units.map_neg, map_one]

