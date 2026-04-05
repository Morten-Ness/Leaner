import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem mk_eq_zero {f : CauSeq _ abv} : CauSeq.Completion.mk f = 0 ↔ LimZero f := by
  have : CauSeq.Completion.mk f = 0 ↔ LimZero (f - 0) := Quotient.eq
  rwa [sub_zero] at this

