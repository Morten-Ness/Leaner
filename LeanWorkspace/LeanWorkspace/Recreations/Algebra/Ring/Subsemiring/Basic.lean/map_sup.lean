import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem map_sup (s t : Subsemiring R) (f : R →+* S) : (s ⊔ t).map f = s.map f ⊔ t.map f := (Subsemiring.gc_map_comap f).l_sup

