import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_lt_self_iff {a : R} : ⌊a⌋ < a ↔ a ∉ Set.range Int.cast := (floor_le a).lt_iff_ne.trans <| (Int.floor_eq_self_iff_mem _).not

