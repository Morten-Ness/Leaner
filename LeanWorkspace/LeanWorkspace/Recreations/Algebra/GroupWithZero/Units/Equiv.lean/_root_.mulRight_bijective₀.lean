import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀]

theorem _root_.mulRight_bijective₀ (a : G₀) (ha : a ≠ 0) : Function.Bijective ((· * a) : G₀ → G₀) := (Equiv.mulRight₀ a ha).bijective

