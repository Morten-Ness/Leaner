import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_sup (S₁ S₂ : Submonoid M) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op := Submonoid.opEquiv.map_sup _ _

