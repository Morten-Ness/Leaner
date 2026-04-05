import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [SetLike S R] [hSR : SubsemiringClass S R] (s : S)

theorem coe_subtype : (SubsemiringClass.subtype s : s → R) = ((↑) : s → R) := rfl

