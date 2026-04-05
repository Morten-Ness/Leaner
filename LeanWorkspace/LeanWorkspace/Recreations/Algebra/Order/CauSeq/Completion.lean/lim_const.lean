import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

variable [IsComplete β abv]

theorem lim_const (x : β) : CauSeq.lim (const abv x) = x := CauSeq.lim_eq_of_equiv_const <| Setoid.refl _

