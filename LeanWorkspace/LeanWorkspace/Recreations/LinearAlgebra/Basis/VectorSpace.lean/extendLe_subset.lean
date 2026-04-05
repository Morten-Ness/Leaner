import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem extendLe_subset (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    Set.range (Module.Basis.extendLe hs hst ht) ⊆ t := (Module.Basis.range_extendLe hs hst ht).symm ▸ hs.extend_subset hst

