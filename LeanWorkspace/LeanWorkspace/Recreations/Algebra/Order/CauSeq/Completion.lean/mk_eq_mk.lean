import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem mk_eq_mk (f : CauSeq _ abv) : @Eq (CauSeq.Completion.Cauchy abv) ⟦f⟧ (CauSeq.Completion.mk f) := rfl

