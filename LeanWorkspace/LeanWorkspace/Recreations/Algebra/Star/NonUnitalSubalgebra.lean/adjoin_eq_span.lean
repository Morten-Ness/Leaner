import Mathlib

open scoped Pointwise

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

theorem adjoin_eq_span (s : Set A) :
    (NonUnitalStarAlgebra.adjoin R s).toSubmodule = Submodule.span R (Subsemigroup.closure (s ∪ star s)) := by
  rw [NonUnitalStarAlgebra.adjoin_toNonUnitalSubalgebra, NonUnitalAlgebra.adjoin_eq_span]

