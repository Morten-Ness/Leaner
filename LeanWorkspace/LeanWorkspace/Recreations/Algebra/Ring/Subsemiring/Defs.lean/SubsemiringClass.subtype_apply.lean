import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [SetLike S R] [hSR : SubsemiringClass S R] (s : S)

theorem subtype_apply (x : s) :
    SubsemiringClass.subtype s x = x := rfl

