import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_iff_eq_add_zsmul : a ≡ b [PMOD p] ↔ ∃ z : ℤ, b = a + z • p := by
  simp_rw [AddCommGroup.modEq_iff_zsmul', sub_eq_iff_eq_add']

-- this roughly matches `Int.modEq_zero_iff_dvd`

