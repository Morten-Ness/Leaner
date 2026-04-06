FAIL
import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem adjoin_univ : NonUnitalAlgebra.adjoin R (Set.univ : Set A) = ⊤ := by
  rw [eq_top_iff]
  intro x hx
  exact NonUnitalAlgebra.subset_adjoin (s := (Set.univ : Set A)) (Set.mem_univ x)
