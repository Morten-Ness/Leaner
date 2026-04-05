import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem inv_comp [One M] [One N] [InvOneClass P] (g : OneHom N P) (f : OneHom M N) :
    (g⁻¹).comp f = (g.comp f)⁻¹ := rfl

