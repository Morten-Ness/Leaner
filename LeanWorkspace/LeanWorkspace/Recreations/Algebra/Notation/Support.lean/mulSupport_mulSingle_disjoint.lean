import Mathlib

variable {ι κ M N P : Type*}

variable [DecidableEq ι] [One M] {i j : ι} {a b : M}

theorem mulSupport_mulSingle_disjoint (ha : a ≠ 1) (hb : b ≠ 1) :
    Disjoint (Function.mulSupport (mulSingle i a)) (Function.mulSupport (mulSingle j b)) ↔ i ≠ j := by
  rw [Pi.mulSupport_mulSingle_of_ne ha, Pi.mulSupport_mulSingle_of_ne hb, disjoint_singleton]

