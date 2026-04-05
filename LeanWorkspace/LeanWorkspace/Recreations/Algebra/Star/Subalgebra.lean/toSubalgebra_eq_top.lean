import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem toSubalgebra_eq_top {S : StarSubalgebra R A} : S.toSubalgebra = ⊤ ↔ S = ⊤ := StarSubalgebra.toSubalgebra_injective.eq_iff' StarSubalgebra.top_toSubalgebra

