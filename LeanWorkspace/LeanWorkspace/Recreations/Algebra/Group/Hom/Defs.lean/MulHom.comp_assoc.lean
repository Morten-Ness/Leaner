import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MulHom.comp_assoc {Q : Type*} [Mul M] [Mul N] [Mul P] [Mul Q]
    (f : M →ₙ* N) (g : N →ₙ* P) (h : P →ₙ* Q) : (h.comp g).comp f = h.comp (g.comp f) := rfl

