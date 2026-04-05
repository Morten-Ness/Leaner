import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.add [AddSemigroup α] [InvolutiveNeg β] (h1 : Function.Antiperiodic f c₁)
    (h2 : Function.Antiperiodic f c₂) : Function.Periodic f (c₁ + c₂) := by simp_all [← add_assoc]

