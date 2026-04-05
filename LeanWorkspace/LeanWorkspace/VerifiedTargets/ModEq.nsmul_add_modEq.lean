import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem nsmul_add_modEq (n : ℕ) : n • p + a ≡ a [PMOD p] := AddCommGroup.modEq_iff_nsmul.mpr ⟨0, n, by simp⟩

