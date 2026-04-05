import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s : Subsemiring R}

variable {σR σS : Type*}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

theorem codRestrict_apply (f : R →+* S) (s : σS) (h : ∀ x, f x ∈ s) (x : R) :
    (f.codRestrict s h x : S) = f x := rfl

