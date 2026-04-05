import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem ofSpan_apply_self (hs : ⊤ ≤ span K s)
    (x : (linearIndepOn_empty K id).extend (empty_subset s)) :
    Module.Basis.ofSpan hs x = x := Module.Basis.extendLe_apply_self (linearIndependent_empty K V) (empty_subset s) hs x

