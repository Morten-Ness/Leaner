import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem lt_of_lt_floor (h : n < ⌊a⌋₊) : ↑n < a := (Nat.cast_lt.2 h).trans_le <| Nat.floor_le (Nat.pos_of_floor_pos <| (Nat.zero_le n).trans_lt h).le

