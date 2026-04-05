import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem ofRat_natCast (n : ℕ) : (CauSeq.Completion.ofRat n : CauSeq.Completion.Cauchy abv) = n := rfl

