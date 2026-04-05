import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [FloorRing k] {b : k}

theorem sub_floor_div_mul_lt (a : k) (hb : 0 < b) : a - ⌊a / b⌋ * b < b := sub_lt_iff_lt_add.2 <| by
    rw [← one_add_mul, ← div_lt_iff₀ hb, add_comm]
    exact Int.lt_floor_add_one _

