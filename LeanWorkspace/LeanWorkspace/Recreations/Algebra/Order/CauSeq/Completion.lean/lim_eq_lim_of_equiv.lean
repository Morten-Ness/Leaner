import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

variable [IsComplete β abv]

theorem lim_eq_lim_of_equiv {f g : CauSeq β abv} (h : f ≈ g) : CauSeq.lim f = CauSeq.lim g := CauSeq.lim_eq_of_equiv_const <| Setoid.trans h <| CauSeq.equiv_lim g

