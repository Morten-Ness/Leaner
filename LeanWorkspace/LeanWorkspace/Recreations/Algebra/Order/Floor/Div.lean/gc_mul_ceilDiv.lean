import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β] [MulActionWithZero α β]

variable [CeilDiv α α] {a b c : α}

theorem gc_mul_ceilDiv (ha : 0 < a) : GaloisConnection (· ⌈/⌉ a) (a * ·) := gc_smul_ceilDiv ha

