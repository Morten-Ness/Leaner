import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.coe_id {M : Type*} [MulOne M] : (MonoidHom.id M : M → M) = _root_.id := rfl

