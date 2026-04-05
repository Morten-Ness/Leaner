import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]

variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem commute_of_mem_adjoin_singleton_of_commute {a b c : A}
    (hc : c ∈ NonUnitalAlgebra.adjoin R {b}) (h : Commute a b) :
    Commute a c := NonUnitalAlgebra.commute_of_mem_adjoin_of_forall_mem_commute hc <| by simpa

