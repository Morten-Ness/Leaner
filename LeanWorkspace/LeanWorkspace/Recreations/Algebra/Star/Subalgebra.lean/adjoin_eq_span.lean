import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem adjoin_eq_span (s : Set A) :
    Subalgebra.toSubmodule (StarAlgebra.adjoin R s).toSubalgebra = span R (Submonoid.closure (s ∪ star s)) := by
  rw [StarAlgebra.adjoin_toSubalgebra, Algebra.adjoin_eq_span]

