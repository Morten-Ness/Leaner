import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.even_nsmul_periodic [AddMonoid α] [InvolutiveNeg β] (h : Function.Antiperiodic f c)
    (n : ℕ) : Function.Periodic f ((2 * n) • c) := mul_nsmul c 2 n ▸ h.periodic.nsmul n

