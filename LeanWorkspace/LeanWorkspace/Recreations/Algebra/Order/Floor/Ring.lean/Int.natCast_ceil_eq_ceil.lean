import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

variable {a : R}

theorem Int.natCast_ceil_eq_ceil (ha : 0 ≤ a) : (⌈a⌉₊ : ℤ) = ⌈a⌉ := by
  rw [← Int.ceil_toNat, Int.toNat_of_nonneg (Int.ceil_nonneg ha)]

