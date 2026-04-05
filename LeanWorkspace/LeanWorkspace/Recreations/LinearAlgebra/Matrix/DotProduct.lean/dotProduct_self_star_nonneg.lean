import Mathlib

variable {m n p R : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [PartialOrder R] [NonUnitalRing R] [StarRing R] [StarOrderedRing R]

theorem dotProduct_self_star_nonneg (v : n → R) : 0 ≤ v ⬝ᵥ star v := Fintype.sum_nonneg fun _ => mul_star_self_nonneg _

