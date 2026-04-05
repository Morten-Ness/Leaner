import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem add_zsmul (z : ℤ) : a ≡ b [PMOD p] → a + z • p ≡ b [PMOD p] := (AddCommGroup.add_zsmul_modEq _).trans

