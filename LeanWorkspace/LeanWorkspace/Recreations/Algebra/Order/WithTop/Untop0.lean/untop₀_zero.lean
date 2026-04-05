import Mathlib

variable {α : Type*}

variable [Zero α]

theorem untop₀_zero : WithTop.untop₀ 0 = (0 : α) := by simp [WithTop.untop₀]

