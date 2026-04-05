import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s : Subsemiring R}

variable {σR σS : Type*}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

theorem rangeS_codRestrict {f : R →+* S} {s : σS} {h : ∀ x, f x ∈ s} :
    RingHom.rangeS (RingHom.codRestrict f s h) = Subsemiring.comap (SubsemiringClass.subtype s) f.rangeS := SetLike.coe_injective <| Set.range_codRestrict h

