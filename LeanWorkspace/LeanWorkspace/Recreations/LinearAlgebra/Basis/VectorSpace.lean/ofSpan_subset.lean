import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem ofSpan_subset (hs : ⊤ ≤ span K s) : Set.range (Module.Basis.ofSpan hs) ⊆ s := Module.Basis.extendLe_subset (linearIndependent_empty K V) (empty_subset s) hs

