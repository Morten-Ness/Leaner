import Mathlib

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A]

theorem NonUnitalStarSubalgebra.toStarSubalgebra_toNonUnitalStarSubalgebra
    (S : NonUnitalStarSubalgebra R A) (h1 : (1 : A) ∈ S) :
    (S.toStarSubalgebra h1).toNonUnitalStarSubalgebra = S := by
  cases S; rfl

