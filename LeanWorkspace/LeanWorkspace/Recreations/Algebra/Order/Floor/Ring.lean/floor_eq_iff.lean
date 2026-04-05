import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem floor_eq_iff : ⌊a⌋ = z ↔ ↑z ≤ a ∧ a < z + 1 := by
  rw [le_antisymm_iff, le_floor, ← Int.lt_add_one_iff, floor_lt, Int.cast_add, Int.cast_one,
    and_comm]

