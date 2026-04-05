import Mathlib

variable (R A B C : Type*) [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B] [NonUnitalNonAssocSemiring C]
  [DistribMulAction R C] [Star C]

theorem coe_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : ⇑(f.prod g) = Pi.prod f g := rfl

