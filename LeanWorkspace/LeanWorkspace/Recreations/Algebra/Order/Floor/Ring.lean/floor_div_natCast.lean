import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [FloorRing k] {a b : k}

theorem floor_div_natCast (a : k) (n : ℕ) : ⌊a / n⌋ = ⌊a⌋ / n := by
  simpa using Int.floor_div_cast_of_nonneg n.cast_nonneg a

