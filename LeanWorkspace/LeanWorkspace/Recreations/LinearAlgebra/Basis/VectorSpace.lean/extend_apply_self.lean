import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem extend_apply_self (hs : LinearIndepOn K id s) (x : hs.extend _) : Module.Basis.extend hs x = x := Module.Basis.mk_apply _ _ _

