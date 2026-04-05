import Mathlib

variable {ι κ M N P : Type*}

variable [DecidableEq ι] [One M] {i j : ι} {a b : M}

theorem mulSupport_mulSingle_of_ne (h : a ≠ 1) : Function.mulSupport (mulSingle i a) = {i} := Pi.mulSupport_mulSingle_subset.antisymm fun x hx ↦ by rwa [Function.mem_mulSupport, hx, mulSingle_eq_same]

