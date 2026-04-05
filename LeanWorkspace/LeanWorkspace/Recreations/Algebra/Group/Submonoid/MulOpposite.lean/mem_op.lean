import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem mem_op {x : Mᵐᵒᵖ} {S : Submonoid M} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

