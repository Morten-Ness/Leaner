import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem sub_right (c : G) (h : a ≡ b [PMOD p]) : a - c ≡ b - c [PMOD p] := h.sub AddCommGroup.modEq_rfl

