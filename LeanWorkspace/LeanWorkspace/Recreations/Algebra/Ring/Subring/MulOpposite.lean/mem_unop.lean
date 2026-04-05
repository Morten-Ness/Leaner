import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem mem_unop {x : R} {S : Subring Rᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

