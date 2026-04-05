import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable {s : Subsemiring R} {σR : Type*} [SetLike σR R] [SubsemiringClass σR R]

theorem restrict_apply (f : R →+* S) {s : σR} (x : s) : f.domRestrict s x = f x := rfl

