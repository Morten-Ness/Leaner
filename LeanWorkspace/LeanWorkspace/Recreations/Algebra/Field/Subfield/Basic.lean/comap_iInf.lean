import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem comap_iInf {ι : Sort*} (f : K →+* L) (s : ι → Subfield L) :
    (iInf s).comap f = ⨅ i, (s i).comap f := (Subfield.gc_map_comap f).u_iInf

