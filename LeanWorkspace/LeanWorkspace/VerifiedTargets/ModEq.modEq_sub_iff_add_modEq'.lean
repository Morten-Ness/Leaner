import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_sub_iff_add_modEq' : a ≡ b - c [PMOD p] ↔ c + a ≡ b [PMOD p] := by
  simp [AddCommGroup.modEq_iff_zsmul', sub_sub]

