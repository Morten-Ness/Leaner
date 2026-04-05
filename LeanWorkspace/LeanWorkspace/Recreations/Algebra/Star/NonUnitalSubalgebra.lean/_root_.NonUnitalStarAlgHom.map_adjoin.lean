import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable (S : NonUnitalStarSubalgebra R A)

variable [StarRing R]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

variable [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]

theorem _root_.NonUnitalStarAlgHom.map_adjoin (f : F) (s : Set A) :
    NonUnitalStarSubalgebra.map f (NonUnitalStarAlgebra.adjoin R s) = NonUnitalStarAlgebra.adjoin R (f '' s) := Set.image_preimage.l_comm_of_u_comm (NonUnitalStarSubalgebra.gc_map_comap f) NonUnitalStarAlgebra.NonUnitalStarAlgebra.gc gi
    NonUnitalStarAlgebra.NonUnitalStarAlgebra.gc gi fun _t => rfl

