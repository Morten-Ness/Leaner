import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem mem_op {x : Aᵐᵒᵖ} {S : Subalgebra R A} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

