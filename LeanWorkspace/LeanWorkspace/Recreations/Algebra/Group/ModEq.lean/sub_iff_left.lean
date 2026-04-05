import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem sub_iff_left (h : a₁ ≡ b₁ [PMOD p]) :
    a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p] := by
  simp [sub_eq_add_neg, h]

