import Mathlib

variable {ι κ M N P : Type*}

variable [DecidableEq ι] [One M] {i j : ι} {a b : M}

theorem mulSupport_mulSingle_subset : Function.mulSupport (mulSingle i a) ⊆ {i} := fun _ hx ↦
  by_contra fun hx' ↦ hx <| mulSingle_eq_of_ne hx' _

