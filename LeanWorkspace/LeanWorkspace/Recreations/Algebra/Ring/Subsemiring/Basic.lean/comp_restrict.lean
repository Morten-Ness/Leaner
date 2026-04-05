import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s : Subsemiring R}

variable {σR σS : Type*}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

theorem comp_restrict (f : R →+* S) (s' : σR) (s : σS) (h : ∀ x ∈ s', f x ∈ s) :
    (SubsemiringClass.subtype s).comp (f.restrict s' s h) = f.comp (SubsemiringClass.subtype s') := rfl

