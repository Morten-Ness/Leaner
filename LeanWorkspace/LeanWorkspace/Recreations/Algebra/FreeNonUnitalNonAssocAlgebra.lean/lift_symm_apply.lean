import Mathlib

open scoped MonoidAlgebra

variable (R X A : Type*) [Semiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem lift_symm_apply (F : FreeNonUnitalNonAssocAlgebra R X →ₙₐ[R] A) :
    (FreeNonUnitalNonAssocAlgebra.lift R).symm F = F ∘ FreeNonUnitalNonAssocAlgebra.of R := rfl

