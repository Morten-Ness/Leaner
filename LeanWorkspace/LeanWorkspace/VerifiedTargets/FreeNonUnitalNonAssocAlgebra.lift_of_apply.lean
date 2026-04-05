import Mathlib

open scoped MonoidAlgebra

variable (R X A : Type*) [Semiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem lift_of_apply (f : X → A) (x) : FreeNonUnitalNonAssocAlgebra.lift R f (FreeNonUnitalNonAssocAlgebra.of R x) = f x := congr_fun (FreeNonUnitalNonAssocAlgebra.of_comp_lift _ f) x

