import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem comap_top (f : R →+* S) : (⊤ : Subsemiring S).comap f = ⊤ := (Subsemiring.gc_map_comap f).u_top

