import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem inv_apply {f : CauSeq β abv} (hf i) : CauSeq.inv f hf i = (f i)⁻¹ := rfl

