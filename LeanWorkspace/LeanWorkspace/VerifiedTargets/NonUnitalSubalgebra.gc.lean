import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem gc : GaloisConnection (NonUnitalAlgebra.adjoin R : Set A → NonUnitalSubalgebra R A) (↑) := fun s S =>
  ⟨fun H => (NonUnitalSubsemiring.subset_closure.trans Submodule.subset_span).trans H,
    fun H => show Submodule.span R _ ≤ S.toSubmodule from Submodule.span_le.mpr <|
      show NonUnitalSubsemiring.closure s ≤ S.toNonUnitalSubsemiring from
        NonUnitalSubsemiring.closure_le.2 H⟩

