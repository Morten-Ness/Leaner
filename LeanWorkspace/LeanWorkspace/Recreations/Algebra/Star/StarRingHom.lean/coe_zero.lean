import Mathlib

variable {A B C : Type*}

variable [NonUnitalNonAssocSemiring A] [StarAddMonoid A]

variable [NonUnitalNonAssocSemiring B] [StarAddMonoid B]

theorem coe_zero : ((0 : A →⋆ₙ+* B) : A → B) = 0 := rfl

