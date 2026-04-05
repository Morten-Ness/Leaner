import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem coe_inv {f : CauSeq β abv} (hf) : ⇑(CauSeq.inv f hf) = (f : ℕ → β)⁻¹ := rfl

