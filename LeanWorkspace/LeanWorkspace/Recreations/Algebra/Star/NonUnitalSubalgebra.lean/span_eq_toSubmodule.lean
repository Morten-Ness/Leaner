import Mathlib

open scoped Pointwise

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

theorem span_eq_toSubmodule {R} [CommSemiring R] [Module R A] (s : NonUnitalStarSubalgebra R A) :
    Submodule.span R (s : Set A) = s.toSubmodule := by
  simp [SetLike.ext'_iff, Submodule.coe_span_eq_self]

