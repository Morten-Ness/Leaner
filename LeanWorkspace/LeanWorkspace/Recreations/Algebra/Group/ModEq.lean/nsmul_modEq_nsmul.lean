import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem nsmul_modEq_nsmul [IsAddTorsionFree M] {n : ℕ} (hn : n ≠ 0) :
    n • a ≡ n • b [PMOD n • p] ↔ a ≡ b [PMOD p] := by
  simp only [AddCommGroup.modEq_iff_nsmul, ← mul_nsmul _ n, mul_nsmul' _ n, ← AddCommGroup.ModEq.nsmul_add, nsmul_right_inj hn]

alias ⟨AddCommGroup.ModEq.nsmul_cancel, _⟩ := nsmul_modEq_nsmul

