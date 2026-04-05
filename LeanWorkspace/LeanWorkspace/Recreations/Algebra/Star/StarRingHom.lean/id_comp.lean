import Mathlib

variable {A B C D : Type*}

variable [NonUnitalNonAssocSemiring A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Star B]

variable [NonUnitalNonAssocSemiring C] [Star C]

variable [NonUnitalNonAssocSemiring D] [Star D]

theorem id_comp (f : A →⋆ₙ+* B) : (NonUnitalStarRingHom.id _).comp f = f := NonUnitalStarRingHom.ext fun _ => rfl

