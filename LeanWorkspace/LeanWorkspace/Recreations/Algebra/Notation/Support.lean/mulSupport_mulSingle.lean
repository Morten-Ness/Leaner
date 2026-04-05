import Mathlib

variable {ι κ M N P : Type*}

variable [DecidableEq ι] [One M] {i j : ι} {a b : M}

theorem mulSupport_mulSingle [DecidableEq M] :
    Function.mulSupport (mulSingle i a) = if a = 1 then ∅ else {i} := by split_ifs with h <;> simp [h]

