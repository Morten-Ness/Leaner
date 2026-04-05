import Mathlib

variable {α : Type*}

theorem nat_ceil_coe [Semiring α] [PartialOrder α] [IsOrderedRing α] [FloorSemiring α]
    (a : { r : α // 0 ≤ r }) :
    ⌈(a : α)⌉₊ = ⌈a⌉₊ := rfl

