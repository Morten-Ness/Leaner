import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem comap_top [IsScalarTower R B B] [SMulCommClass R B B]
    (f : A →ₙₐ[R] B) : (⊤ : NonUnitalSubalgebra R B).comap f = ⊤ := NonUnitalAlgebra.eq_top_iff.2 fun _ => NonUnitalAlgebra.mem_top

