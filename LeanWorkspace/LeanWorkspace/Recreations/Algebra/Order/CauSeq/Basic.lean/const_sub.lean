import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem const_sub (x y : β) : CauSeq.const (x - y) = CauSeq.const x - CauSeq.const y := rfl

