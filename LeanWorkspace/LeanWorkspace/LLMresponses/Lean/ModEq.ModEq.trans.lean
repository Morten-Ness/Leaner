import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem ModEq.trans (hab : a ≡ b [PMOD p]) (hbc : b ≡ c [PMOD p]) :
    a ≡ c [PMOD p] := by
  exact hab.trans hbc
