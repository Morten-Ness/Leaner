import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀]

theorem _root_.mulLeft_bijective₀ (a : G₀) (ha : a ≠ 0) : Function.Bijective (a * · : G₀ → G₀) := (Equiv.mulLeft₀ a ha).bijective

