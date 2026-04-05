import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem limZero_congr {f g : CauSeq β abv} (h : f ≈ g) : CauSeq.LimZero f ↔ CauSeq.LimZero g := ⟨fun l => by simpa using CauSeq.add_limZero (Setoid.symm h) l, fun l => by simpa using CauSeq.add_limZero h l⟩

