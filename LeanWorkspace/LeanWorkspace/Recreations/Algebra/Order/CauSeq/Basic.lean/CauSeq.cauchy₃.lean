import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem cauchy₃ (f : CauSeq β abv) {ε} : 0 < ε → ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - f j) < ε := IsCauSeq.cauchy₃ f.2

