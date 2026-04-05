import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem coe_add (f g : CauSeq β abv) : ⇑(f + g) = (f : ℕ → β) + g := rfl

