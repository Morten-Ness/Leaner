import Mathlib

variable {A B C : Type*}

variable [NonUnitalNonAssocSemiring A] [StarAddMonoid A]

variable [NonUnitalNonAssocSemiring B] [StarAddMonoid B]

theorem zero_apply (a : A) : (0 : A →⋆ₙ+* B) a = 0 := rfl

