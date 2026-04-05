import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_eq_self {a : R} : fract a = a ↔ 0 ≤ a ∧ a < 1 := Int.fract_eq_iff.trans <| and_assoc.symm.trans <| and_iff_left ⟨0, by simp⟩

