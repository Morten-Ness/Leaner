import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem zsmul_add_modEq (z : ℤ) : z • p + a ≡ a [PMOD p] := AddCommGroup.modEq_iff_zsmul.mpr ⟨-z, by simp⟩

