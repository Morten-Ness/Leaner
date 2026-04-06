FAIL
import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_sup (S₁ S₂ : Subalgebra R Aᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop := by
  ext a
  constructor
  · intro ha
    change MulOpposite.op a ∈ S₁ ⊔ S₂ at ha
    exact Subalgebra.mulMem_sup (s := S₁.unop) (t := S₂.unop) ha
  · intro ha
    change MulOpposite.op a ∈ S₁ ⊔ S₂
    exact Subalgebra.opMem_sup (s := S₁) (t := S₂) ha
