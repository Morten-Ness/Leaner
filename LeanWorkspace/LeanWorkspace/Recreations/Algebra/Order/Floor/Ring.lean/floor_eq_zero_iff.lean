import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem floor_eq_zero_iff : ⌊a⌋ = 0 ↔ a ∈ Ico (0 : R) 1 := by simp [Int.floor_eq_iff]

