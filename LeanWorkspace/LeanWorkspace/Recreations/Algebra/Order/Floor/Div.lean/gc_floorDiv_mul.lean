import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β] [MulActionWithZero α β]

variable [FloorDiv α α] {a b c : α}

theorem gc_floorDiv_mul (ha : 0 < a) : GaloisConnection (a * ·) (· ⌊/⌋ a) := gc_floorDiv_smul ha

