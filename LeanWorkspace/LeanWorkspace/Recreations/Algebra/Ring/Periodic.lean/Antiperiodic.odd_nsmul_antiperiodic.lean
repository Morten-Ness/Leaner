import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.odd_nsmul_antiperiodic [AddMonoid α] [InvolutiveNeg β] (h : Function.Antiperiodic f c)
    (n : ℕ) : Function.Antiperiodic f ((2 * n + 1) • c) := fun x => by
  rw [add_nsmul, one_nsmul, ← add_assoc, h, h.even_nsmul_periodic]

