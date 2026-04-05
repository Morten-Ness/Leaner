import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem extendLe_apply_self (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t)
    (x : hs.extend hst) : Module.Basis.extendLe hs hst ht x = x := Module.Basis.mk_apply _ _ _

