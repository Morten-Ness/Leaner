import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

theorem cauchy (f : CauSeq β abv) : ∀ {ε}, 0 < ε → ∃ i, ∀ j ≥ i, abv (f j - f i) < ε := @f.2

