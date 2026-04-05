import Mathlib

variable {ι α β : Type*}

variable (α β) [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β]
  [SMulZeroClass α β]

variable [FloorDiv α β] {a : α} {b c : β}

theorem gc_floorDiv_smul (ha : 0 < a) : GaloisConnection (a • · : β → β) (· ⌊/⌋ a) := FloorDiv.floorDiv_gc ha

