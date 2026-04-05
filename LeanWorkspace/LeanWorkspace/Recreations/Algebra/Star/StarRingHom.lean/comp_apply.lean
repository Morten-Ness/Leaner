import Mathlib

variable {A B C D : Type*}

variable [NonUnitalNonAssocSemiring A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Star B]

variable [NonUnitalNonAssocSemiring C] [Star C]

variable [NonUnitalNonAssocSemiring D] [Star D]

theorem comp_apply (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) (a : A) : NonUnitalStarRingHom.comp f g a = f (g a) := rfl

