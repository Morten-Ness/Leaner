import Mathlib

variable {R K : Type*}

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

theorem floor_div_eq_div (m n : ℕ) : ⌊(m : K) / n⌋₊ = m / n := by
  convert Nat.floor_div_natCast (m : K) n
  rw [m.floor_natCast]

