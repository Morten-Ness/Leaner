import Mathlib

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A]

theorem StarSubalgebra.toNonUnitalStarSubalgebra_toStarSubalgebra (S : StarSubalgebra R A) :
    S.toNonUnitalStarSubalgebra.toStarSubalgebra S.one_mem' = S := by cases S; rfl

