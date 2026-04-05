import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem ofRat_zero : (CauSeq.Completion.ofRat 0 : CauSeq.Completion.Cauchy abv) = 0 := rfl

