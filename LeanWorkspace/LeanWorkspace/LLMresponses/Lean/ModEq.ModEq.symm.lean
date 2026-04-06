import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem ModEq.symm (h : a ≡ b [PMOD p]) : b ≡ a [PMOD p] := h.symm
