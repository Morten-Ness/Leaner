import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem exists_basis : ∃ s : Set V, Nonempty (Module.Basis s K V) := ⟨Module.Basis.ofVectorSpaceIndex K V, ⟨Module.Basis.ofVectorSpace K V⟩⟩

