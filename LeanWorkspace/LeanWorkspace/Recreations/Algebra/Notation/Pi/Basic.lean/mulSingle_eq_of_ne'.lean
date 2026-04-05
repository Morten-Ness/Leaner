import Mathlib

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

theorem mulSingle_eq_of_ne' {i i' : ι} (h : i ≠ i') (x : M i) : Pi.mulSingle i x i' = 1 := Pi.mulSingle_eq_of_ne h.symm x

