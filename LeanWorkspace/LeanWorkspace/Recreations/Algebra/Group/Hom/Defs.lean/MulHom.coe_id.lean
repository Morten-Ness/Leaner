import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MulHom.coe_id {M : Type*} [Mul M] : (MulHom.id M : M → M) = _root_.id := rfl

