import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem range_extendLe (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    Set.range (Module.Basis.extendLe hs hst ht) = hs.extend hst := by
  rw [Module.Basis.coe_extendLe, Subtype.range_coe_subtype, setOf_mem_eq]

