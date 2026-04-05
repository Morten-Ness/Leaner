import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem ofVectorSpaceIndex.linearIndependent :
    LinearIndependent K ((↑) : Module.Basis.ofVectorSpaceIndex K V → V) := by
  convert (Module.Basis.ofVectorSpace K V).linearIndependent
  ext x
  rw [Module.Basis.ofVectorSpace_apply_self]

