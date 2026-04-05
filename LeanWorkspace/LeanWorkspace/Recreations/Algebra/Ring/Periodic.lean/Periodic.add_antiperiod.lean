import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.add_antiperiod [AddSemigroup α] [Neg β] (h1 : Function.Periodic f c₁)
    (h2 : Function.Antiperiodic f c₂) : Function.Antiperiodic f (c₁ + c₂) := by simp_all [← add_assoc]

