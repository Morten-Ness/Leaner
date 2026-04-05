import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_eq_bot {S : Subsemigroup Mᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := Subsemigroup.unop_injective.eq_iff' Subsemigroup.unop_bot

