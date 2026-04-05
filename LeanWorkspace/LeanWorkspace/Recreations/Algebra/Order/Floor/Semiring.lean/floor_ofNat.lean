import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem floor_ofNat (n : ℕ) [n.AtLeastTwo] : ⌊(ofNat(n) : R)⌋₊ = ofNat(n) := Nat.floor_natCast _

