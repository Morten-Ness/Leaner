import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem add_nsmul (n : ℕ) : a ≡ b [PMOD p] → a + n • p ≡ b [PMOD p] := (AddCommGroup.add_nsmul_modEq _).trans

