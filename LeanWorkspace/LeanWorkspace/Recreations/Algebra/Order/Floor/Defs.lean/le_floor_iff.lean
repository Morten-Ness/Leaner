import Mathlib

variable {F α β : Type*}

variable [Semiring α] [PartialOrder α] [FloorSemiring α] {a : α} {n : ℕ}

theorem le_floor_iff (ha : 0 ≤ a) : n ≤ ⌊a⌋₊ ↔ (n : α) ≤ a := FloorSemiring.gc_floor ha

