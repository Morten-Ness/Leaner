import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem zsmul_modEq_zero (z : ℤ) : z • p ≡ 0 [PMOD p] := AddCommGroup.modEq_iff_zsmul.mpr ⟨-z, by simp⟩

