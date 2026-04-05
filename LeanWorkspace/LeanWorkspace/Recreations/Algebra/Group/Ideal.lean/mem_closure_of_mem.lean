import Mathlib

variable {M : Type*}

variable [Mul M] {s t : Set M} {x : M}

theorem mem_closure_of_mem (hx : x ∈ s) : x ∈ closure s := SubMulAction.mem_closure_of_mem hx

