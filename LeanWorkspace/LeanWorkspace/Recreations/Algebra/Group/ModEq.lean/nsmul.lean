import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem nsmul {n : ℕ} (h : a ≡ b [PMOD p]) : n • a ≡ n • b [PMOD n • p] := by
  rw [AddCommGroup.modEq_iff_nsmul] at *
  rcases h with ⟨k, l, h⟩
  use k, l
  rw [← mul_nsmul, mul_nsmul', ← nsmul_add, h, nsmul_add, ← mul_nsmul, mul_nsmul']

