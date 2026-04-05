import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

theorem commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A}
    (hb : b ∈ NonUnitalStarAlgebra.adjoin R s) (h : ∀ b ∈ s, Commute a b) (h_star : ∀ b ∈ s, Commute a (star b)) :
    Commute a b := NonUnitalAlgebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun b hb ↦
    hb.elim (h b) (by simpa using h_star (star b))

