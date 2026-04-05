import Mathlib

variable {A B C D : Type*}

variable [NonUnitalNonAssocSemiring A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Star B]

variable [NonUnitalNonAssocSemiring C] [Star C]

variable [NonUnitalNonAssocSemiring D] [Star D]

theorem coe_comp (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) : ⇑(NonUnitalStarRingHom.comp f g) = f ∘ g := rfl

