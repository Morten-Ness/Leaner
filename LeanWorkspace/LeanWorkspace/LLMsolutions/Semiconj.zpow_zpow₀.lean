FAIL
import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem zpow_zpow₀ (h : Commute a b) (m n : ℤ) : Commute (a ^ m) (b ^ n) := by
  rcases em (a = 0) with rfl | ha
  · simp
  · rcases em (b = 0) with rfl | hb
    · simp
    · exact (h.units_right ha hb).zpow_zpow m n |> fun h' => by simpa using h'
