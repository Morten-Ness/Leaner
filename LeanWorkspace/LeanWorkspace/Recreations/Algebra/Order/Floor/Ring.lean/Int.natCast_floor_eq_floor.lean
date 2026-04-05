import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

variable {a : R}

theorem Int.natCast_floor_eq_floor (ha : 0 ≤ a) : (⌊a⌋₊ : ℤ) = ⌊a⌋ := by
  rw [← Int.floor_toNat, Int.toNat_of_nonneg (Int.floor_nonneg.2 ha)]

