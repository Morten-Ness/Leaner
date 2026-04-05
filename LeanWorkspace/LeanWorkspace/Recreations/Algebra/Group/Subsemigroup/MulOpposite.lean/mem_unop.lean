import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem mem_unop {x : M} {S : Subsemigroup Mᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

