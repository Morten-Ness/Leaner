import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem fract_add (a b : R) : ∃ z : ℤ, fract (a + b) - fract a - fract b = z := ⟨⌊a⌋ + ⌊b⌋ - ⌊a + b⌋, by unfold fract; grind⟩

