import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem zsmul_modEq_zsmul [IsAddTorsionFree G] (hn : z ≠ 0) :
    z • a ≡ z • b [PMOD z • p] ↔ a ≡ b [PMOD p] := by
  simp [AddCommGroup.modEq_iff_zsmul, ← zsmul_sub, zsmul_comm, zsmul_right_inj hn]

alias ⟨AddCommGroup.ModEq.zsmul_cancel, _⟩ := zsmul_modEq_zsmul

