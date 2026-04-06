import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem add_zsmul_modEq (z : ℤ) : a + z • p ≡ a [PMOD p] := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (Int.modEq_iff_dvd' (a + z • p) a p).2 ⟨z, by abel⟩
