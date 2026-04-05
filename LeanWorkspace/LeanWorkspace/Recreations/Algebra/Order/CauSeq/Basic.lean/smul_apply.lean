import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

variable {G : Type*} [SMul G β] [IsScalarTower G β β]

theorem smul_apply (a : G) (f : CauSeq β abv) (i : ℕ) : (a • f) i = a • f i := rfl

