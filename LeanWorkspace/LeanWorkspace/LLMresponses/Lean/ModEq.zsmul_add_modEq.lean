import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem zsmul_add_modEq (z : ℤ) : z • p + a ≡ a [PMOD p] := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    AddCommGroup.ModEq.int_smul_left a z p
