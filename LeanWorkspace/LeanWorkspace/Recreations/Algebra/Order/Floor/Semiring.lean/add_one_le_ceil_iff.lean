import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

theorem add_one_le_ceil_iff : n + 1 ≤ ⌈a⌉₊ ↔ (n : R) < a := by
  rw [← Nat.lt_ceil, Nat.add_one_le_iff]

