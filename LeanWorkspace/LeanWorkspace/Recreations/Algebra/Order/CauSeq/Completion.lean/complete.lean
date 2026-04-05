import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

variable [IsComplete β abv]

theorem complete : ∀ s : CauSeq β abv, ∃ b : β, s ≈ const abv b := IsComplete.isComplete

