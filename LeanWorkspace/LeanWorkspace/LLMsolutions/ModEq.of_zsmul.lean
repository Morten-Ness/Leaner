FAIL
import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem of_zsmul (h : a ≡ b [PMOD z • p]) : a ≡ b [PMOD p] := by
  rw [AddCommGroup.modEq_iff_eq_int_smul_sub] at h ⊢
  rcases h with ⟨k, hk⟩
  refine ⟨z * k, ?_⟩
  rw [hk, zsmul_eq_mul, zsmul_eq_mul, mul_assoc]
