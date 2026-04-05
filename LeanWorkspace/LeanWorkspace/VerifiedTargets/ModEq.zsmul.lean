import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem zsmul (h : a ≡ b [PMOD p]) : z • a ≡ z • b [PMOD z • p] := by
  rw [AddCommGroup.modEq_iff_zsmul] at *
  rcases h with ⟨m, h⟩
  use m
  rw [← zsmul_sub, ← h, ← mul_zsmul, ← mul_zsmul']

