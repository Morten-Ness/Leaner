import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem coe_ofSpan (hs : ⊤ ≤ span K s) : ⇑(Module.Basis.ofSpan hs) = ((↑) : _ → _) := funext (Module.Basis.ofSpan_apply_self hs)

