import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem preimage_floor_singleton (m : ℤ) : (floor : R → ℤ) ⁻¹' {m} = Ico (m : R) (m + 1) := ext fun _ => Int.floor_eq_iff

