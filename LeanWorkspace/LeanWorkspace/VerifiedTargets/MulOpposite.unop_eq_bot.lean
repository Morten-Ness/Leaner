import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_eq_bot {S : Submonoid Mᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := Submonoid.unop_injective.eq_iff' Submonoid.unop_bot

