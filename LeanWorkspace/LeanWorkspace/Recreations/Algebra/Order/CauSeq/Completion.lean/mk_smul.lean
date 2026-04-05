import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem mk_smul {γ : Type*} [SMul γ β] [IsScalarTower γ β β] (c : γ) (f : CauSeq β abv) :
    c • CauSeq.Completion.mk f = CauSeq.Completion.mk (c • f) := rfl

