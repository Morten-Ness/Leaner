import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem modEq_refl (a : M) : a ≡ a [PMOD p] := ⟨0, 0, by simp⟩

