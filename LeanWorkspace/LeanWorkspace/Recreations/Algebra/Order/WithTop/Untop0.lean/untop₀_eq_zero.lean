import Mathlib

variable {α : Type*}

variable [Zero α]

theorem untop₀_eq_zero {a : WithTop α} :
    a.untop₀ = 0 ↔ a = 0 ∨ a = ⊤ := by simp [WithTop.untop₀]

