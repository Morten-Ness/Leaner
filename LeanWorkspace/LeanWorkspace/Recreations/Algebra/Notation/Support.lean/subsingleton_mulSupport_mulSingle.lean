import Mathlib

variable {ι κ M N P : Type*}

variable [DecidableEq ι] [One M] {i j : ι} {a b : M}

theorem subsingleton_mulSupport_mulSingle : (Function.mulSupport (mulSingle i a)).Subsingleton := by
  classical
  rw [Pi.mulSupport_mulSingle]
  split_ifs with h <;> simp

