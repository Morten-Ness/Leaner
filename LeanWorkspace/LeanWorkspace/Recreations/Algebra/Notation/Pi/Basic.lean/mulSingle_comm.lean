import Mathlib

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

variable {M : Type*} [One M]

theorem mulSingle_comm (i : ι) (x : M) (j : ι) :
    (Pi.mulSingle i x : ι → M) j = (Pi.mulSingle j x : ι → M) i := by simp [Pi.mulSingle_apply, eq_comm]

