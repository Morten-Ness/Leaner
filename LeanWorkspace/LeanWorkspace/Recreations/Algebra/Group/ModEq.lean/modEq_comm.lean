import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p] := ⟨.symm, .symm⟩

