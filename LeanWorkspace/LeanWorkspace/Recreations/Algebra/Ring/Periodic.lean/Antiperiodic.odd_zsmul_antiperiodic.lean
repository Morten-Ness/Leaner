import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.odd_zsmul_antiperiodic [AddGroup α] [InvolutiveNeg β] (h : Function.Antiperiodic f c)
    (n : ℤ) : Function.Antiperiodic f ((2 * n + 1) • c) := by
  intro x
  rw [add_zsmul, one_zsmul, ← add_assoc, h, h.even_zsmul_periodic]

