import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [MulAction A M]

theorem of_compHom : letI := MulAction.compHom M (algebraMap R A : R →* A); IsScalarTower R A M :=
  letI := MulAction.compHom M (algebraMap R A : R →* A); IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

