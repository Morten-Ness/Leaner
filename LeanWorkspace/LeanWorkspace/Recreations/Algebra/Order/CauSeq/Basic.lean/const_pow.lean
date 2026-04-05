import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem const_pow (x : β) (n : ℕ) : CauSeq.const (x ^ n) = CauSeq.const x ^ n := rfl

