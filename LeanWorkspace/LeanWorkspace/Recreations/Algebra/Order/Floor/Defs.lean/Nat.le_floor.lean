import Mathlib

variable {F α β : Type*}

variable [Semiring α] [PartialOrder α] [FloorSemiring α] {a : α} {n : ℕ}

theorem le_floor [IsOrderedRing α] (h : (n : α) ≤ a) : n ≤ ⌊a⌋₊ := (Nat.le_floor_iff <| n.cast_nonneg.trans h).2 h

