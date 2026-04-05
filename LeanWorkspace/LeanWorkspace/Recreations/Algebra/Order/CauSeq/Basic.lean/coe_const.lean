import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem coe_const (x : β) : (CauSeq.const x : ℕ → β) = Function.const ℕ x := rfl

