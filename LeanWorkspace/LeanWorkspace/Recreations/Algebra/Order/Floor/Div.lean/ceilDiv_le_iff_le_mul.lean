import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β] [MulActionWithZero α β]

variable [CeilDiv α α] {a b c : α}

theorem ceilDiv_le_iff_le_mul (ha : 0 < a) : b ⌈/⌉ a ≤ c ↔ b ≤ a * c := ceilDiv_le_iff_le_smul ha

