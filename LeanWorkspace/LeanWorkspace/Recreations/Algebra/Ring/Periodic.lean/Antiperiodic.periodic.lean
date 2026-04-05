import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.periodic [AddMonoid α] [InvolutiveNeg β]
    (h : Function.Antiperiodic f c) : Function.Periodic f (2 • c) := by simp [two_nsmul, ← add_assoc, h _]

