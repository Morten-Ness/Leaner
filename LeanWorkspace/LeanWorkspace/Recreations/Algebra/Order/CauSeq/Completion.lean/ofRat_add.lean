import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem ofRat_add (x y : β) :
    CauSeq.Completion.ofRat (x + y) = (CauSeq.Completion.ofRat x + CauSeq.Completion.ofRat y : CauSeq.Completion.Cauchy abv) := congr_arg CauSeq.Completion.mk (const_add _ _)

