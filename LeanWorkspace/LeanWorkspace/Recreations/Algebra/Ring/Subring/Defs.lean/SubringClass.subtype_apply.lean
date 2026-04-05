import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [SetLike S R] [hSR : SubringClass S R] (s : S)

theorem subtype_apply (x : s) :
    SubringClass.subtype s x = x := rfl

