import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_iff_zsmul' : a ≡ b [PMOD p] ↔ ∃ m : ℤ, b - a = m • p := by
  simp only [AddCommGroup.modEq_iff_zsmul, eq_comm]

