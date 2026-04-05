import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem floor_of_nonpos (ha : a ≤ 0) : ⌊a⌋₊ = 0 := ha.lt_or_eq.elim FloorSemiring.floor_of_neg <| by
    rintro rfl
    exact Nat.floor_zero

