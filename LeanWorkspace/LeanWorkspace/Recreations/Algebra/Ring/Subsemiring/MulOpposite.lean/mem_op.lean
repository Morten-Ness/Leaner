import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem mem_op {x : Rᵐᵒᵖ} {S : Subsemiring R} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

