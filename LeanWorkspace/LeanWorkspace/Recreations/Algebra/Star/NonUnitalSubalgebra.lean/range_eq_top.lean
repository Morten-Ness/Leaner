import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

theorem range_eq_top [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]
    (f : F) : NonUnitalStarAlgHom.range f = (⊤ : NonUnitalStarSubalgebra R B) ↔
      Function.Surjective f := NonUnitalStarAlgebra.eq_top_iff

