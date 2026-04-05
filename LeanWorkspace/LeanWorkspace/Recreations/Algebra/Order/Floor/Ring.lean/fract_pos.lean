import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_pos : 0 < fract a ↔ a ≠ ⌊a⌋ := (Int.fract_nonneg a).lt_iff_ne.trans <| ne_comm.trans sub_ne_zero

