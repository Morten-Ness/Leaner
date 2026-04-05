import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem bounded' (f : CauSeq β abv) (x : α) : ∃ r > x, ∀ i, abv (f i) < r := IsCauSeq.bounded' f.2 x

