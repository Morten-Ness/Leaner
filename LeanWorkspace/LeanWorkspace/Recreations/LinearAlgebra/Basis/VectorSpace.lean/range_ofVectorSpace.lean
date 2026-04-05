import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem range_ofVectorSpace : Set.range (Module.Basis.ofVectorSpace K V) = Module.Basis.ofVectorSpaceIndex K V := Module.Basis.range_extend _

