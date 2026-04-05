import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem mk_eq {f g : CauSeq _ abv} : CauSeq.Completion.mk f = CauSeq.Completion.mk g ↔ LimZero (f - g) := Quotient.eq

