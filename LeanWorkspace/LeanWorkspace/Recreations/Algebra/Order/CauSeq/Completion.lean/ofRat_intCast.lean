import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem ofRat_intCast (z : ℤ) : (CauSeq.Completion.ofRat z : CauSeq.Completion.Cauchy abv) = z := rfl

