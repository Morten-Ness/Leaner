import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem sub_modEq_iff_modEq_add : a - b ≡ c [PMOD p] ↔ a ≡ c + b [PMOD p] := by
  constructor
  · intro h
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h.add_right b
  · intro h
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h.sub_right b
