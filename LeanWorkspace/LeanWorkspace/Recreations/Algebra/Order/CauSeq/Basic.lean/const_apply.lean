import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem const_apply (x : β) (i : ℕ) : (CauSeq.const x : ℕ → β) i = x := rfl

