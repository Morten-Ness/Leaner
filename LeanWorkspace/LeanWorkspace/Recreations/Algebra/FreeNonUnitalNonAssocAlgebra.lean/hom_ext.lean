import Mathlib

open scoped MonoidAlgebra

variable (R X A : Type*) [Semiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem hom_ext {F₁ F₂ : FreeNonUnitalNonAssocAlgebra R X →ₙₐ[R] A}
    (h : ∀ x, F₁ (FreeNonUnitalNonAssocAlgebra.of R x) = F₂ (FreeNonUnitalNonAssocAlgebra.of R x)) : F₁ = F₂ := (FreeNonUnitalNonAssocAlgebra.lift R).symm.injective <| funext h

