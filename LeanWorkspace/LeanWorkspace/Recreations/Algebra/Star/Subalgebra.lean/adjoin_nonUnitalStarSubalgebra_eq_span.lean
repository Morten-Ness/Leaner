import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem adjoin_nonUnitalStarSubalgebra_eq_span (s : NonUnitalStarSubalgebra R A) :
    (StarAlgebra.adjoin R (s : Set A)).toSubalgebra.toSubmodule = span R {1} ⊔ s.toSubmodule := by
  rw [StarAlgebra.adjoin_eq_span, Submonoid.closure_eq_one_union, span_union,
    ← NonUnitalStarAlgebra.adjoin_eq_span, NonUnitalStarAlgebra.adjoin_eq]

