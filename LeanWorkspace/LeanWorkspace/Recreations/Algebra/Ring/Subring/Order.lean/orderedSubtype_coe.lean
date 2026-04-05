import Mathlib

variable {R S : Type*} [Ring R] [PartialOrder R] [SetLike S R] [SubringClass S R]

theorem orderedSubtype_coe (s : Subring R) : Subring.orderedSubtype s = Subring.subtype s := rfl

