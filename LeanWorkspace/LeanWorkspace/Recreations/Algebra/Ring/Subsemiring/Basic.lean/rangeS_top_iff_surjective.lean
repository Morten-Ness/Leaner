import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s : Subsemiring R}

variable {σR σS : Type*}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

theorem rangeS_top_iff_surjective {f : R →+* S} :
    f.rangeS = (⊤ : Subsemiring S) ↔ Function.Surjective f := SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_rangeS, coe_top]) Set.range_eq_univ

