import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable {s : Subsemiring R} {σR : Type*} [SetLike σR R] [SubsemiringClass σR R]

theorem mem_eqLocusS {f g : R →+* S} {x : R} : x ∈ f.eqLocusS g ↔ f x = g x := Iff.rfl

