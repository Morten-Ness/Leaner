import Mathlib

section

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem coe_extend (hs : LinearIndepOn K id s) : ⇑(Module.Basis.extend hs) = ((↑) : _ → _) := funext (Module.Basis.extend_apply_self hs)

end

section

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem coe_ofVectorSpace : ⇑(Module.Basis.ofVectorSpace K V) = ((↑) : _ → _) := funext fun x => Module.Basis.ofVectorSpace_apply_self K V x

end

section

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem exists_basis : ∃ s : Set V, Nonempty (Module.Basis s K V) := ⟨Module.Basis.ofVectorSpaceIndex K V, ⟨Module.Basis.ofVectorSpace K V⟩⟩

end

section

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem ofVectorSpaceIndex.linearIndependent :
    LinearIndependent K ((↑) : Module.Basis.ofVectorSpaceIndex K V → V) := by
  convert (Module.Basis.ofVectorSpace K V).linearIndependent
  ext x
  rw [Module.Basis.ofVectorSpace_apply_self]

end

section

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem ofVectorSpace_apply_self (x : Module.Basis.ofVectorSpaceIndex K V) : Module.Basis.ofVectorSpace K V x = x := by
  unfold Module.Basis.ofVectorSpace
  exact Module.Basis.mk_apply _ _ _

end
