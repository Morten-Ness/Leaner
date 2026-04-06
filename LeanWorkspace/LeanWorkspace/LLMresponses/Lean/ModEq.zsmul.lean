FAIL
import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem zsmul (h : a ≡ b [PMOD p]) : z • a ≡ z • b [PMOD z • p] := by
  rw [AddCommGroup.modEq_iff_eq_dvd] at h ⊢
  rcases h with ⟨d, hd⟩
  refine ⟨d, ?_⟩
  rw [← zsmul_sub, hd, zsmul_zsmul]
