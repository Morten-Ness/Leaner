import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem adjoin_mono {s t : Set A} (H : s ⊆ t) : NonUnitalAlgebra.adjoin R s ≤ NonUnitalAlgebra.adjoin R t := NonUnitalAlgebra.gc.monotone_l H

