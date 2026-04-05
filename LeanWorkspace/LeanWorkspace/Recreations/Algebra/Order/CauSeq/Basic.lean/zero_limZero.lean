import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem zero_limZero : CauSeq.LimZero (0 : CauSeq β abv)
  | ε, ε0 => ⟨0, fun j _ => by simpa [abv_zero abv] using ε0⟩
