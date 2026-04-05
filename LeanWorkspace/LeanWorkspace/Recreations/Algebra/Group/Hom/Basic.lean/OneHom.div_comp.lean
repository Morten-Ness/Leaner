import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem div_comp [One M] [One N] [DivisionMonoid P] (g₁ g₂ : OneHom N P) (f : OneHom M N) :
    (g₁ / g₂).comp f = g₁.comp f / g₂.comp f := rfl

