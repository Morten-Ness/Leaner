FAIL
import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem toSubmodule_bot : (⊥ : NonUnitalSubalgebra R A).toSubmodule = ⊥ := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact hx ▸ (show (0 : A) ∈ (⊥ : NonUnitalSubalgebra R A).toSubmodule from by simp)
