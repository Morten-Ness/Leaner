import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem map_iSup {ι : Sort*} (f : K →+* L) (s : ι → Subfield K) :
    (iSup s).map f = ⨆ i, (s i).map f := (Subfield.gc_map_comap f).l_iSup

