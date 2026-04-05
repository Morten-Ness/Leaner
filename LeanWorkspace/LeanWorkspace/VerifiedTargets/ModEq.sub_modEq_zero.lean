import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem sub_modEq_zero : a - b ≡ 0 [PMOD p] ↔ a ≡ b [PMOD p] := by simp [AddCommGroup.sub_modEq_iff_modEq_add]

-- this matches `Int.modEq_iff_add_fac`

