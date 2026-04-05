import Mathlib

variable {A B C D : Type*}

variable [NonUnitalNonAssocSemiring A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Star B]

variable [NonUnitalNonAssocSemiring C] [Star C]

variable [NonUnitalNonAssocSemiring D] [Star D]

theorem comp_id (f : A →⋆ₙ+* B) : f.comp (NonUnitalStarRingHom.id _) = f := NonUnitalStarRingHom.ext fun _ => rfl

