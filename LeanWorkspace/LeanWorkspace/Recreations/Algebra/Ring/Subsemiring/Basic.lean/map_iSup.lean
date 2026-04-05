import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem map_iSup {ι : Sort*} (f : R →+* S) (s : ι → Subsemiring R) :
    (iSup s).map f = ⨆ i, (s i).map f := (Subsemiring.gc_map_comap f).l_iSup

