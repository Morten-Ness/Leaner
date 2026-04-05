import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem coe_one : ⇑(1 : CauSeq β abv) = 1 := rfl

