import Mathlib

variable {R A M : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A]

variable {C : Type*} [SetLike C R] [SubsemiringClass C R]

theorem algebraMap_ofSubring {R : Type*} [CommRing R] (S : Subring R) :
    (algebraMap S R : S →+* R) = S.subtype := rfl

