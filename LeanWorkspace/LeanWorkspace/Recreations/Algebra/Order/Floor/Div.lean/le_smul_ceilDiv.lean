import Mathlib

variable {ι α β : Type*}

variable (α β) [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β]
  [SMulZeroClass α β]

variable [CeilDiv α β] {a : α} {b c : β}

theorem le_smul_ceilDiv (ha : 0 < a) : b ≤ a • (b ⌈/⌉ a) := (ceilDiv_le_iff_le_smul ha).1 le_rfl

