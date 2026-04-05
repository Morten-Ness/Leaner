import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem sub_left_cancel' (c : G) : c - a ≡ c - b [PMOD p] → a ≡ b [PMOD p] := AddCommGroup.modEq_rfl.sub_left_cancel

