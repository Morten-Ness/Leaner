import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem range_extend (hs : LinearIndepOn K id s) :
    Set.range (Module.Basis.extend hs) = hs.extend (subset_univ _) := by
  rw [Module.Basis.coe_extend, Subtype.range_coe_subtype, setOf_mem_eq]

