import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem add_right (c : M) (h : a ≡ b [PMOD p]) : a + c ≡ b + c [PMOD p] := AddCommGroup.ModEq.add h AddCommGroup.modEq_rfl

