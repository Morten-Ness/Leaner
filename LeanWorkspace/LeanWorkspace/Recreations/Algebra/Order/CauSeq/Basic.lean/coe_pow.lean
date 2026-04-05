import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem coe_pow (f : CauSeq β abv) (n : ℕ) : ⇑(f ^ n) = (f : ℕ → β) ^ n := rfl

