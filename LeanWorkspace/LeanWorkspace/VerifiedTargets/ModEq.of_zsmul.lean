import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem of_zsmul (h : a ≡ b [PMOD z • p]) : a ≡ b [PMOD p] := by
  rw [AddCommGroup.modEq_iff_zsmul] at *
  rcases h with ⟨m, h⟩
  simp [← h, ← mul_zsmul]

