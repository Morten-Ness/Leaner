import Mathlib

variable {R A M : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A]

variable {C : Type*} [SetLike C R] [SubsemiringClass C R]

theorem algebraMap_ofSubsemiring (S : Subsemiring R) :
    (algebraMap S R : S →+* R) = S.subtype := rfl

