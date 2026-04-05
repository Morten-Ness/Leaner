import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.even_zsmul_periodic [AddGroup α] [InvolutiveNeg β] (h : Function.Antiperiodic f c)
    (n : ℤ) : Function.Periodic f ((2 * n) • c) := by
  rw [mul_comm, mul_zsmul, two_zsmul, ← two_nsmul]
  exact h.periodic.zsmul n

