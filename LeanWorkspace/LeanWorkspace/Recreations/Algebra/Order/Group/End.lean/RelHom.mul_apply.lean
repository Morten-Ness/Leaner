import Mathlib

variable {α : Type*} {r : α → α → Prop}

theorem mul_apply (e₁ e₂ : r →r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

