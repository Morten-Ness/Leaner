import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem const_inv {x : β} (hx : x ≠ 0) :
    CauSeq.const abv x⁻¹ = CauSeq.inv (CauSeq.const abv x) (by rwa [CauSeq.const_limZero]) := rfl

