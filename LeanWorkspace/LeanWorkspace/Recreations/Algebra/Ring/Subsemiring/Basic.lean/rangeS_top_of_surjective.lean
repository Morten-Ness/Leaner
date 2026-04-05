import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s : Subsemiring R}

variable {σR σS : Type*}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

theorem rangeS_top_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    f.rangeS = (⊤ : Subsemiring S) := RingHom.rangeS_top_iff_surjective.2 hf

