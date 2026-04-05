import Mathlib

variable {R K : Type*}

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

theorem floor_div_ofNat (a : K) (n : ℕ) [n.AtLeastTwo] :
    ⌊a / ofNat(n)⌋₊ = ⌊a⌋₊ / ofNat(n) := Nat.floor_div_natCast a n

