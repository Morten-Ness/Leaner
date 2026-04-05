import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem comap_iInf {ι : Sort*} (f : R →+* S) (s : ι → Subsemiring S) :
    (iInf s).comap f = ⨅ i, (s i).comap f := (Subsemiring.gc_map_comap f).u_iInf

