import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]

variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem commute_of_mem_adjoin_self {a b : A} (hb : b ∈ NonUnitalAlgebra.adjoin R {a}) :
    Commute a b := NonUnitalAlgebra.commute_of_mem_adjoin_singleton_of_commute hb rfl

