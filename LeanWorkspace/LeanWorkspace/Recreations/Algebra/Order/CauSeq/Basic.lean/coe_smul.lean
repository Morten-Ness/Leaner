import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

variable {G : Type*} [SMul G β] [IsScalarTower G β β]

theorem coe_smul (a : G) (f : CauSeq β abv) : ⇑(a • f) = a • (f : ℕ → β) := rfl

