import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem cauchy₂ (f : CauSeq β abv) {ε} :
    0 < ε → ∃ i, ∀ j ≥ i, ∀ k ≥ i, abv (f j - f k) < ε := IsCauSeq.cauchy₂ f.2

