import Mathlib

variable {α : Type u}

theorem recOneCoe_one {motive : WithOne α → Sort*} (h₁ h₂) :
    WithOne.recOneCoe h₁ h₂ (1 : WithOne α) = (h₁ : motive 1) := rfl

