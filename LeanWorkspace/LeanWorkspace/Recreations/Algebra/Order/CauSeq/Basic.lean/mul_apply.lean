import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem mul_apply (f g : CauSeq β abv) (i : ℕ) : (f * g) i = f i * g i := rfl

