import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem mk_add (f g : CauSeq β abv) : CauSeq.Completion.mk f + CauSeq.Completion.mk g = CauSeq.Completion.mk (f + g) := rfl

