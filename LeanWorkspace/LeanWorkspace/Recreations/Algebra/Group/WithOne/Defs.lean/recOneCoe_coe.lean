import Mathlib

variable {α : Type u}

theorem recOneCoe_coe {motive : WithOne α → Sort*} (h₁ h₂) (a : α) :
    WithOne.recOneCoe h₁ h₂ (a : WithOne α) = (h₂ : ∀ a : α, motive a) a := rfl

