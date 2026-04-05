import Mathlib

variable {ι α β : Type*}

variable (α β) [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β]
  [SMulZeroClass α β]

variable [CeilDiv α β] {a : α} {b c : β}

theorem ceilDiv_zero (b : β) : b ⌈/⌉ (0 : α) = 0 := by simp

