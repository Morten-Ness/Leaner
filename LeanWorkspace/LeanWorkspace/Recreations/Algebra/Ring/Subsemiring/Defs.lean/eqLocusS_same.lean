import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable {s : Subsemiring R} {σR : Type*} [SetLike σR R] [SubsemiringClass σR R]

theorem eqLocusS_same (f : R →+* S) : f.eqLocusS f = ⊤ := SetLike.ext fun _ => eq_self_iff_true _

