import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem lt_succ_floor (a : R) : a < ⌊a⌋₊.succ := Nat.lt_of_floor_lt <| Nat.lt_succ_self _

