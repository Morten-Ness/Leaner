import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem inv_apply {M N} [One M] [InvOneClass N] (f : OneHom M N) (x : M) :
    f⁻¹ x = (f x)⁻¹ := rfl

