import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem subset_extend {s : Set V} (hs : LinearIndepOn K id s) : s ⊆ hs.extend (Set.subset_univ _) := hs.subset_extend _

