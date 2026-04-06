import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_sub_iff_add_modEq : a ≡ b - c [PMOD p] ↔ a + c ≡ b [PMOD p] := by
  constructor
  · intro h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h.add_right c
  · intro h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h.add_right (-c)
