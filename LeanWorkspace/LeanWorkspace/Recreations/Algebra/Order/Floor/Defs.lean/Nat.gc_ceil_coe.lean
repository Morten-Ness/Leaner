import Mathlib

variable {F α β : Type*}

variable [Semiring α] [PartialOrder α] [FloorSemiring α] {a : α} {n : ℕ}

theorem gc_ceil_coe : GaloisConnection (Nat.ceil : α → ℕ) (↑) := FloorSemiring.gc_ceil

