import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_sub_iff_add_modEq : a ≡ b - c [PMOD p] ↔ a + c ≡ b [PMOD p] := AddCommGroup.modEq_sub_iff_add_modEq'.trans <| by rw [add_comm]

