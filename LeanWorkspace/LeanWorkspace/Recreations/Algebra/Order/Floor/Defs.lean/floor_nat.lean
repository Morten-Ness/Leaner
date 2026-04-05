import Mathlib

variable {F α β : Type*}

variable [Semiring α] [PartialOrder α] [FloorSemiring α] {a : α} {n : ℕ}

theorem floor_nat : (Nat.floor : ℕ → ℕ) = id := rfl

