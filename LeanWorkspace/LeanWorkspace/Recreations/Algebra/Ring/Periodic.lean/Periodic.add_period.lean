import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.add_period [AddSemigroup α] (h1 : Function.Periodic f c₁) (h2 : Function.Periodic f c₂) :
    Function.Periodic f (c₁ + c₂) := by simp_all [← add_assoc]

