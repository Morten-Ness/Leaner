import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem coe_inv {M N} [One M] [InvOneClass N] (f : OneHom M N) : ⇑(f⁻¹) = (⇑f)⁻¹ := rfl

