FAIL
import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem zpow_left₀ (h : Commute a b) (m : ℤ) : Commute (a ^ m) b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [Commute]
  · simpa using h.units_zpow_left ha m
