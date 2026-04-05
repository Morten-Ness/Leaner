import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem sub_iff_right (h : a₂ ≡ b₂ [PMOD p]) :
    a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p] := by
  simp [h, sub_eq_add_neg]

protected alias ⟨sub_left_cancel, sub⟩ := AddCommGroup.ModEq.sub_iff_left

protected alias ⟨sub_right_cancel, _⟩ := AddCommGroup.ModEq.sub_iff_right

