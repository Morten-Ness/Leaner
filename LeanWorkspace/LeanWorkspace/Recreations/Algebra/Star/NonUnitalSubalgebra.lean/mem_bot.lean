import Mathlib

open scoped Pointwise

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

theorem mem_bot {x : A} : x ∈ (⊥ : NonUnitalStarSubalgebra R A) ↔ x = 0 := show x ∈ NonUnitalAlgebra.adjoin R (∅ ∪ star ∅ : Set A) ↔ x = 0 by
    rw [Set.star_empty, Set.union_empty, NonUnitalAlgebra.adjoin_empty, NonUnitalAlgebra.mem_bot]

