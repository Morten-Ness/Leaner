import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_eq_top {S : Subsemigroup Mᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := Subsemigroup.unop_injective.eq_iff' Subsemigroup.unop_top

