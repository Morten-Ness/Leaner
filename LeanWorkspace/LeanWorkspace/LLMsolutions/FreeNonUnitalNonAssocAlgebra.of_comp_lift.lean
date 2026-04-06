import Mathlib

open scoped MonoidAlgebra

variable (R X A : Type*) [Semiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem of_comp_lift (f : X → A) : FreeNonUnitalNonAssocAlgebra.lift R f ∘ FreeNonUnitalNonAssocAlgebra.of R = f := by
  funext x
  simp [Function.comp]
