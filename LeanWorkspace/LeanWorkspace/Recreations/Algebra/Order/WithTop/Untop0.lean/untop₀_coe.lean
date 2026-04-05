import Mathlib

variable {α : Type*}

variable [Zero α]

theorem untop₀_coe (a : α) : (a : WithTop α).untop₀ = a := rfl

