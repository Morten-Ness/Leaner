import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

variable [IsComplete β abv]

theorem lim_mul (f : CauSeq β abv) (x : β) : CauSeq.lim f * x = CauSeq.lim (f * const abv x) := by
  rw [← CauSeq.lim_mul_lim, CauSeq.lim_const]

