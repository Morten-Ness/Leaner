FAIL
import Mathlib

open scoped MonoidAlgebra

variable (R X A : Type*) [Semiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem lift_comp_of (F : FreeNonUnitalNonAssocAlgebra R X →ₙₐ[R] A) : FreeNonUnitalNonAssocAlgebra.lift R (F ∘ FreeNonUnitalNonAssocAlgebra.of R) = F := by
  apply FreeNonUnitalNonAssocAlgebra.hom_ext
  intro x
  simp [FreeNonUnitalNonAssocAlgebra.lift, FreeNonUnitalNonAssocAlgebra.ι]
