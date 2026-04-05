import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_sup (S₁ S₂ : Subsemigroup M) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op := Subsemigroup.opEquiv.map_sup _ _

