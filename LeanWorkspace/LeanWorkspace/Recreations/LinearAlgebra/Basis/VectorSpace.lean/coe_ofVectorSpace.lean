import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem coe_ofVectorSpace : ⇑(Module.Basis.ofVectorSpace K V) = ((↑) : _ → _) := funext fun x => Module.Basis.ofVectorSpace_apply_self K V x

