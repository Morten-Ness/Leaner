import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem sub_right_cancel' (c : G) : a - c ≡ b - c [PMOD p] → a ≡ b [PMOD p] := by
  intro h
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h.add_right c
