import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem add_zsmul_modEq (z : ℤ) : a + z • p ≡ a [PMOD p] := AddCommGroup.modEq_iff_zsmul.mpr ⟨-z, by simp⟩

