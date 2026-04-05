import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β] [MulActionWithZero α β]

variable [FloorDiv α α] {a b c : α}

theorem le_floorDiv_iff_mul_le (ha : 0 < a) : c ≤ b ⌊/⌋ a ↔ a • c ≤ b := le_floorDiv_iff_smul_le ha

