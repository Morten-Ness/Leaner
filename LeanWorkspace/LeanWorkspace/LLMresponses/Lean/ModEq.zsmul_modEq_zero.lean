import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem zsmul_modEq_zero (z : ℤ) : z • p ≡ 0 [PMOD p] := by
  simpa [Int.modEq_iff_dvd, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (dvd_refl z)
