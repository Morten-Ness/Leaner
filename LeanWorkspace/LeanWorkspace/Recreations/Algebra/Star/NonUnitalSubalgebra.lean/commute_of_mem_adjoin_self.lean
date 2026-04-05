import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

theorem commute_of_mem_adjoin_self {a b : A} [IsStarNormal a] (hb : b ∈ NonUnitalStarAlgebra.adjoin R {a}) :
    Commute a b := NonUnitalStarAlgebra.commute_of_mem_adjoin_singleton_of_commute hb rfl (isStarNormal_iff a |>.mp inferInstance).symm

