import Mathlib

section

open scoped MonoidAlgebra

variable (R X A : Type*) [Semiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem hom_ext {F₁ F₂ : FreeNonUnitalNonAssocAlgebra R X →ₙₐ[R] A}
    (h : ∀ x, F₁ (FreeNonUnitalNonAssocAlgebra.of R x) = F₂ (FreeNonUnitalNonAssocAlgebra.of R x)) : F₁ = F₂ := (FreeNonUnitalNonAssocAlgebra.lift R).symm.injective <| funext h

end

section

open scoped MonoidAlgebra

variable (R X A : Type*) [Semiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem lift_comp_of (F : FreeNonUnitalNonAssocAlgebra R X →ₙₐ[R] A) : FreeNonUnitalNonAssocAlgebra.lift R (F ∘ FreeNonUnitalNonAssocAlgebra.of R) = F := (FreeNonUnitalNonAssocAlgebra.lift R).apply_symm_apply F

end

section

open scoped MonoidAlgebra

variable (R X A : Type*) [Semiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem lift_of_apply (f : X → A) (x) : FreeNonUnitalNonAssocAlgebra.lift R f (FreeNonUnitalNonAssocAlgebra.of R x) = f x := congr_fun (FreeNonUnitalNonAssocAlgebra.of_comp_lift _ f) x

end

section

open scoped MonoidAlgebra

variable (R X A : Type*) [Semiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem lift_unique (f : X → A) (F : FreeNonUnitalNonAssocAlgebra R X →ₙₐ[R] A) :
    F ∘ FreeNonUnitalNonAssocAlgebra.of R = f ↔ F = FreeNonUnitalNonAssocAlgebra.lift R f := (FreeNonUnitalNonAssocAlgebra.lift R).symm_apply_eq

end

section

open scoped MonoidAlgebra

variable (R X A : Type*) [Semiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem of_comp_lift (f : X → A) : FreeNonUnitalNonAssocAlgebra.lift R f ∘ FreeNonUnitalNonAssocAlgebra.of R = f := (FreeNonUnitalNonAssocAlgebra.lift R).left_inv f

end
