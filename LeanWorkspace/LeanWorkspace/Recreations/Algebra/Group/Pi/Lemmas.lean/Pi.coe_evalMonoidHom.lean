import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [(i : I) → MulOneClass (f i)]

theorem Pi.coe_evalMonoidHom (i : I) : ⇑(evalMonoidHom f i) = Function.eval i := rfl

