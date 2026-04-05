import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem mem_op {x : Mᵐᵒᵖ} {S : Subsemigroup M} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

