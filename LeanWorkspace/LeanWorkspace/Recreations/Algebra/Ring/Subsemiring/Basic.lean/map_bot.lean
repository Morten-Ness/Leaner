import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem map_bot (f : R →+* S) : (⊥ : Subsemiring R).map f = ⊥ := (Subsemiring.gc_map_comap f).l_bot

