import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

variable {G : Type*} [SMul G β] [IsScalarTower G β β]

theorem const_smul (a : G) (x : β) : CauSeq.const (a • x) = a • CauSeq.const x := rfl

