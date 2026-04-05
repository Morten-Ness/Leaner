import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem ofRat_injective : Function.Injective (CauSeq.Completion.ofRat : β → CauSeq.Completion.Cauchy abv) := fun x y h => by
  simpa [CauSeq.Completion.ofRat, CauSeq.Completion.mk_eq, ← const_sub, const_limZero, sub_eq_zero] using h

