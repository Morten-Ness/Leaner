import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem mem_unop {x : M} {S : Submonoid Mᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

