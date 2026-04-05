import Mathlib

variable {α : Type*}

variable [Zero α]

theorem untop₀_top : WithTop.untop₀ ⊤ = (0 : α) := by simp [WithTop.untop₀]

