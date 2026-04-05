import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

theorem le_ceil (a : R) : a ≤ ⌈a⌉₊ := ceil_le.1 le_rfl

