import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem ceil_lt_add_one (ha : 0 ≤ a) : (⌈a⌉₊ : R) < a + 1 := lt_ceil.1 <| (Nat.lt_succ_self _).trans_le (Nat.ceil_add_one ha).ge

