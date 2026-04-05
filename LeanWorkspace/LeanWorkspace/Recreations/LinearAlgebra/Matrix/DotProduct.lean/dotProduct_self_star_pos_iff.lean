import Mathlib

variable {m n p R : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [PartialOrder R] [NonUnitalRing R] [StarRing R] [StarOrderedRing R]

variable [NoZeroDivisors R]

theorem dotProduct_self_star_pos_iff {v : n → R} : 0 < dotProduct v (star v) ↔ v ≠ 0 := by
  simpa using Matrix.dotProduct_star_self_pos_iff (v := star v)

