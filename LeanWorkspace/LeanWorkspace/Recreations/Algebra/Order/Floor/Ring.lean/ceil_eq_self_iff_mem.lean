import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_eq_self_iff_mem (a : R) : ⌈a⌉ = a ↔ a ∈ Set.range Int.cast := by
  aesop

