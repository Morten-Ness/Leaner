import Mathlib

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

variable {M : Type*} [One M]

theorem mulSingle_apply (i : ι) (x : M) (i' : ι) :
    (Pi.mulSingle i x : ι → M) i' = if i' = i then x else 1 := Function.update_apply (1 : ι → M) i x i'

-- Porting note: added type ascription (_ : ι → M)

