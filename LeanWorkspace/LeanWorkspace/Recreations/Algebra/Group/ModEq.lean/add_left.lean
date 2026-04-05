import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem add_left (c : M) (h : a ≡ b [PMOD p]) : c + a ≡ c + b [PMOD p] := AddCommGroup.ModEq.add AddCommGroup.modEq_rfl h

