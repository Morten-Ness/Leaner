import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

theorem commute_of_mem_adjoin_singleton_of_commute {a b c : A}
    (hc : c ∈ NonUnitalStarAlgebra.adjoin R {b}) (h : Commute a b) (h_star : Commute a (star b)) :
    Commute a c := NonUnitalStarAlgebra.commute_of_mem_adjoin_of_forall_mem_commute hc (by simpa) (by simpa)

