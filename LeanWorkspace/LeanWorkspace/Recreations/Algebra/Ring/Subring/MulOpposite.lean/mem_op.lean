import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem mem_op {x : Rᵐᵒᵖ} {S : Subring R} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

