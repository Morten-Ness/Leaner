import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s : Subsemiring R}

variable {σR σS : Type*}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

theorem eq_of_eqOn_sdense {s : Set R} (hs : Subsemiring.closure s = ⊤) {f g : R →+* S} (h : s.EqOn f g) :
    f = g := RingHom.eq_of_eqOn_stop <| hs ▸ RingHom.eqOn_sclosure h

