import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem pos_of_floor_pos (h : 0 < ⌊a⌋₊) : 0 < a := (le_or_gt a 0).resolve_left fun ha => lt_irrefl 0 <| by rwa [Nat.floor_of_nonpos ha] at h

