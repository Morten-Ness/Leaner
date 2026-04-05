import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

variable [IsComplete β abv]

theorem lim_sub (f g : CauSeq β abv) : CauSeq.lim f - CauSeq.lim g = CauSeq.lim (f - g) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← CauSeq.lim_neg, CauSeq.lim_add f (-g)]

