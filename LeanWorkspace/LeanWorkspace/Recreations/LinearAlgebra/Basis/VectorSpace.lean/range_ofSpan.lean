import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem range_ofSpan (hs : ⊤ ≤ span K s) :
    Set.range (Module.Basis.ofSpan hs) = (linearIndepOn_empty K id).extend (empty_subset s) := by
  rw [Module.Basis.coe_ofSpan, Subtype.range_coe_subtype, setOf_mem_eq]

