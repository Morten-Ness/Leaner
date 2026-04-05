import Mathlib

variable {m n p R : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [PartialOrder R] [NonUnitalRing R] [StarRing R] [StarOrderedRing R]

variable [NoZeroDivisors R]

theorem dotProduct_star_self_eq_zero {v : n → R} : star v ⬝ᵥ v = 0 ↔ v = 0 := (Fintype.sum_eq_zero_iff_of_nonneg fun _ => star_mul_self_nonneg _).trans <|
    by simp [funext_iff, mul_eq_zero]

