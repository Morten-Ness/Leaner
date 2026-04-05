import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem _root_.NonUnitalAlgHom.map_adjoin [IsScalarTower R B B] [SMulCommClass R B B]
    (f : F) (s : Set A) : NonUnitalSubalgebra.map f (NonUnitalAlgebra.adjoin R s) = NonUnitalAlgebra.adjoin R (f '' s) := Set.image_preimage.l_comm_of_u_comm (NonUnitalSubalgebra.gc_map_comap f) NonUnitalAlgebra.NonUnitalAlgebra.gc gi
    NonUnitalAlgebra.NonUnitalAlgebra.gc gi fun _t => rfl

