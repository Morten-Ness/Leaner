import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem mk_pow (n : ℕ) (f : CauSeq β abv) : CauSeq.Completion.mk f ^ n = CauSeq.Completion.mk (f ^ n) := rfl

