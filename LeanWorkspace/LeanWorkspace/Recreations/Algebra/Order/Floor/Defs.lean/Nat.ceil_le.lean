import Mathlib

variable {F α β : Type*}

variable [Semiring α] [PartialOrder α] [FloorSemiring α] {a : α} {n : ℕ}

theorem ceil_le : ⌈a⌉₊ ≤ n ↔ a ≤ n := Nat.gc_ceil_coe _ _

