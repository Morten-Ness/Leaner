import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem mem_unop {x : R} {S : Subsemiring Rᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

