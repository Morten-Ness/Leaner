import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem nsmul_add (n : ℕ) : a ≡ b [PMOD p] → n • p + a ≡ b [PMOD p] := (AddCommGroup.nsmul_add_modEq _).trans

