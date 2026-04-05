import Mathlib

open scoped MonoidAlgebra

variable (R X A : Type*) [Semiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem lift_unique (f : X → A) (F : FreeNonUnitalNonAssocAlgebra R X →ₙₐ[R] A) :
    F ∘ FreeNonUnitalNonAssocAlgebra.of R = f ↔ F = FreeNonUnitalNonAssocAlgebra.lift R f := (FreeNonUnitalNonAssocAlgebra.lift R).symm_apply_eq

