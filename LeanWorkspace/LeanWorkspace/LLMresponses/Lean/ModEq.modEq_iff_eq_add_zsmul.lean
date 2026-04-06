FAIL
import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_iff_eq_add_zsmul : a ≡ b [PMOD p] ↔ ∃ z : ℤ, b = a + z • p := by
  rw [AddCommGroup.modeq_iff_eq_zsmul_sub]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [eq_sub_iff_add_eq] at hz
    simpa [add_comm, add_left_comm, add_assoc] using hz
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [eq_sub_iff_add_eq]
    simpa [add_comm, add_left_comm, add_assoc] using hz
