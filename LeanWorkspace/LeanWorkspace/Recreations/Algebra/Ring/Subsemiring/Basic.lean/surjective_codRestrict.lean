import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s : Subsemiring R}

variable {σR σS : Type*}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

theorem surjective_codRestrict {f : R →+* S} {s : σS} {h : ∀ x, f x ∈ s} :
    Function.Surjective (RingHom.codRestrict f s h) ↔ f.rangeS = ofClass s := (Set.surjective_codRestrict h).trans <| .symm <| SetLike.coe_set_eq.symm

