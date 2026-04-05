import Mathlib

variable {ι α β : Type*}

variable (α β) [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β]
  [SMulZeroClass α β]

variable [FloorDiv α β] {a : α} {b c : β}

theorem smul_floorDiv_le (ha : 0 < a) : a • (b ⌊/⌋ a) ≤ b := (le_floorDiv_iff_smul_le ha).1 le_rfl

