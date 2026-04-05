import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem self_modEq_zero : p ≡ 0 [PMOD p] := AddCommGroup.modEq_iff_nsmul.mpr ⟨0, 1, by simp [one_nsmul]⟩

