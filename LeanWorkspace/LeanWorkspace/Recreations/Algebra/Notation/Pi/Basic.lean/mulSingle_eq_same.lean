import Mathlib

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

theorem mulSingle_eq_same (i : ι) (x : M i) : Pi.mulSingle i x i = x := Function.update_self i x _

