import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem ofRat_one : (CauSeq.Completion.ofRat 1 : CauSeq.Completion.Cauchy abv) = 1 := rfl

