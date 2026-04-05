import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_eq_floor_add_one_iff_notMem (a : R) : ⌈a⌉ = ⌊a⌋ + 1 ↔ a ∉ Set.range Int.cast := by
  refine ⟨fun h ht => ?_, fun h => ?_⟩
  · have := ((Int.floor_eq_self_iff_mem _).mpr ht).trans ((Int.ceil_eq_self_iff_mem _).mpr ht).symm
    linarith [Int.cast_inj.mp this]
  · apply le_antisymm (Int.ceil_le_floor_add_one _)
    rw [add_one_le_iff, lt_ceil]
    exact lt_of_le_of_ne (Int.floor_le a) ((iff_false_right h).mp (Int.floor_eq_self_iff_mem a))

