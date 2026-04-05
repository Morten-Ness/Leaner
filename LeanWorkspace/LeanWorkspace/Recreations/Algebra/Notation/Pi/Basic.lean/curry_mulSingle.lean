import Mathlib

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

variable {M : Type*} [One M]

variable [DecidableEq ι']

theorem curry_mulSingle (i : ι × ι') (b : M) :
    curry (Pi.mulSingle i b) = Pi.mulSingle i.1 (Pi.mulSingle i.2 b) := curry_update _ _ _

