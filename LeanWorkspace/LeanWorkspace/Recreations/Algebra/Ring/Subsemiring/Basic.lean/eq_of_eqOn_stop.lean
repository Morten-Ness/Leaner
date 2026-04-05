import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s : Subsemiring R}

variable {σR σS : Type*}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

theorem eq_of_eqOn_stop {f g : R →+* S} (h : Set.EqOn f g (⊤ : Subsemiring R)) : f = g := ext fun _ => h (mem_top _)

