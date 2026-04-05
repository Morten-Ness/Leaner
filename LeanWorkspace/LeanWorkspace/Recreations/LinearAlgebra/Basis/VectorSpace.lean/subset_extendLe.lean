import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem subset_extendLe (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    s ⊆ Set.range (Module.Basis.extendLe hs hst ht) := (Module.Basis.range_extendLe hs hst ht).symm ▸ Module.Basis.subset_extend hs hst

