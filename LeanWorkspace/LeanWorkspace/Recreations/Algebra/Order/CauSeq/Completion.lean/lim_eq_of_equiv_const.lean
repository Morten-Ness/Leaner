import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

variable [IsComplete β abv]

theorem lim_eq_of_equiv_const {f : CauSeq β abv} {x : β} (h : f ≈ CauSeq.const abv x) : CauSeq.lim f = x := (CauSeq.eq_lim_of_const_equiv <| Setoid.symm h).symm

