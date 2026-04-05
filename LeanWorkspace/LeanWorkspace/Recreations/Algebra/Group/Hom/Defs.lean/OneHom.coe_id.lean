import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem OneHom.coe_id {M : Type*} [One M] : (OneHom.id M : M → M) = _root_.id := rfl

