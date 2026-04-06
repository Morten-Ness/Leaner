import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem not_modEq_iff_ne_add_zsmul : ¬a ≡ b [PMOD p] ↔ ∀ z : ℤ, b ≠ a + z • p := by
  rw [AddCommGroup.modEq_iff_eq_add_zsmul]
  constructor
  · intro h z hz
    apply h
    exact ⟨z, hz⟩
  · intro h hab
    rcases hab with ⟨z, hz⟩
    exact h z hz
