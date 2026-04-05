import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem add_nsmul_modEq (n : ℕ) : a + n • p ≡ a [PMOD p] := AddCommGroup.modEq_iff_nsmul.mpr ⟨0, n, by simp [add_comm]⟩

