import Mathlib

variable {α β : Type*}

theorem unop_inj {x y : αᵐᵒᵖ} : MulOpposite.unop x = MulOpposite.unop y ↔ x = y := MulOpposite.unop_injective.eq_iff

attribute [nolint simpComm] AddOpposite.unop_inj

