import Mathlib

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

variable {M : Type*} [One M]

variable [DecidableEq ι']

theorem uncurry_mulSingle_mulSingle (i : ι) (i' : ι') (b : M) :
    uncurry (Pi.mulSingle i (Pi.mulSingle i' b)) = Pi.mulSingle (i, i') b := uncurry_update_update _ _ _ _

