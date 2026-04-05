import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_top : (⊤ : Submonoid Mᵐᵒᵖ).unop = ⊤ := rfl

