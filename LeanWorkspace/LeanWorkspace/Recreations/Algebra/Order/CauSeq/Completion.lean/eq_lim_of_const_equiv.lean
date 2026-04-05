import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

variable [IsComplete β abv]

theorem eq_lim_of_const_equiv {f : CauSeq β abv} {x : β} (h : CauSeq.const abv x ≈ f) : x = CauSeq.lim f := const_equiv.mp <| Setoid.trans h <| CauSeq.equiv_lim f

