import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem sub_modEq_zero : a - b ≡ 0 [PMOD p] ↔ a ≡ b [PMOD p] := by
  constructor
  · intro h
    simpa [sub_eq_add_neg] using h.add_right b
  · intro h
    simpa [sub_eq_add_neg] using h.sub_right b
