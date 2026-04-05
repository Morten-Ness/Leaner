import Mathlib

variable {R A M : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A]

variable {C : Type*} [SetLike C R] [SubsemiringClass C R]

theorem coe_algebraMap_ofSubsemiring (S : C) : (algebraMap S R : S → R) = Subtype.val := rfl

