import Mathlib

variable {ι κ M N P : Type*}

variable [DecidableEq ι] [One M] {i j : ι} {a b : M}

theorem mulSupport_mulSingle_one : Function.mulSupport (mulSingle i (1 : M)) = ∅ := by simp

