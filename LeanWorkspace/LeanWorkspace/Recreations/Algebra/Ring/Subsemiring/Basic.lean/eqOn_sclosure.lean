import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s : Subsemiring R}

variable {σR σS : Type*}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

theorem eqOn_sclosure {f g : R →+* S} {s : Set R} (h : Set.EqOn f g s) : Set.EqOn f g (Subsemiring.closure s) := show Subsemiring.closure s ≤ f.eqLocusS g from Subsemiring.closure_le.2 h

