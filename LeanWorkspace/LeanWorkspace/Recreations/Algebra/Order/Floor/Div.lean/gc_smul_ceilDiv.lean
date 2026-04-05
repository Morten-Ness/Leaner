import Mathlib

variable {ι α β : Type*}

variable (α β) [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β]
  [SMulZeroClass α β]

variable [CeilDiv α β] {a : α} {b c : β}

theorem gc_smul_ceilDiv (ha : 0 < a) : GaloisConnection (· ⌈/⌉ a) (a • · : β → β) := CeilDiv.ceilDiv_gc ha

