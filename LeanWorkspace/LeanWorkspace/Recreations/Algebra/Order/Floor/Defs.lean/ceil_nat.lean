import Mathlib

variable {F α β : Type*}

variable [Semiring α] [PartialOrder α] [FloorSemiring α] {a : α} {n : ℕ}

theorem ceil_nat : (Nat.ceil : ℕ → ℕ) = id := rfl

