import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem pow_apply (f : CauSeq β abv) (n i : ℕ) : (f ^ n) i = f i ^ n := rfl

