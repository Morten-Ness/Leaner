import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

theorem ext {f g : CauSeq β abv} (h : ∀ i, f i = g i) : f = g := Subtype.ext (funext h)

