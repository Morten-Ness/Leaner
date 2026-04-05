import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem le_antisymm {f g : CauSeq α abs} (fg : f ≤ g) (gf : g ≤ f) : f ≈ g := fg.resolve_left (not_lt_of_ge gf)

