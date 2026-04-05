import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

variable [IsComplete β abv]

theorem equiv_lim (s : CauSeq β abv) : s ≈ const abv (CauSeq.lim s) := Classical.choose_spec (CauSeq.complete s)

