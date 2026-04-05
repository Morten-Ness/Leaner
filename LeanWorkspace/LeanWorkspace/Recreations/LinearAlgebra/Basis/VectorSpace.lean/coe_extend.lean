import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem coe_extend (hs : LinearIndepOn K id s) : ⇑(Module.Basis.extend hs) = ((↑) : _ → _) := funext (Module.Basis.extend_apply_self hs)

