import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem ModEq.symm (h : a ≡ b [PMOD p]) : b ≡ a [PMOD p] := by
  rw [AddCommGroup.modEq_iff_nsmul] at *
  rcases h with ⟨m, n, h⟩
  exact ⟨n, m, h.symm⟩

