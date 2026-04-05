import Mathlib

variable {A B C D : Type*}

variable [NonUnitalNonAssocSemiring A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Star B]

variable [NonUnitalNonAssocSemiring C] [Star C]

variable [NonUnitalNonAssocSemiring D] [Star D]

theorem coe_mk (f : A →ₙ+* B) (h) : ((⟨f, h⟩ : A →⋆ₙ+* B) : A → B) = f := rfl

