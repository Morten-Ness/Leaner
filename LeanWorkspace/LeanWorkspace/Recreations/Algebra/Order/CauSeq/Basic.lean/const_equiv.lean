import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem const_equiv {x y : β} : CauSeq.const x ≈ CauSeq.const y ↔ x = y := show CauSeq.LimZero _ ↔ _ by rw [← CauSeq.const_sub, CauSeq.const_limZero, sub_eq_zero]

