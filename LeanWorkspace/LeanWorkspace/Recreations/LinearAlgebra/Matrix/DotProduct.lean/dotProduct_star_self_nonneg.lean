import Mathlib

variable {m n p R : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [PartialOrder R] [NonUnitalRing R] [StarRing R] [StarOrderedRing R]

theorem dotProduct_star_self_nonneg (v : n → R) : 0 ≤ star v ⬝ᵥ v := Fintype.sum_nonneg fun _ => star_mul_self_nonneg _

