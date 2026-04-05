import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem comap_inf (s t : Subsemiring S) (f : R →+* S) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f := (Subsemiring.gc_map_comap f).u_inf

