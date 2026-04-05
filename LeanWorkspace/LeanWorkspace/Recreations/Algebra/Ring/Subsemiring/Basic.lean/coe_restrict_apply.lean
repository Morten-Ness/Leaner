import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s : Subsemiring R}

variable {σR σS : Type*}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

theorem coe_restrict_apply (f : R →+* S) (s' : σR) (s : σS) (h : ∀ x ∈ s', f x ∈ s) (x : s') :
    (f.restrict s' s h x : S) = f x := rfl

