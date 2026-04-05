import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MulHom.coe_comp [Mul M] [Mul N] [Mul P] (g : N →ₙ* P) (f : M →ₙ* N) :
    ↑(g.comp f) = g ∘ f := rfl

