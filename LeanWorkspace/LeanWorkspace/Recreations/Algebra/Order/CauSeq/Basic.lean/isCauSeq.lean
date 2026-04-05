import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

theorem isCauSeq (f : CauSeq β abv) : IsCauSeq abv f := f.2

