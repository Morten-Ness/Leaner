import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem mem_closure_of_mem {s : Set M} {x : M} (hx : x ∈ s) : x ∈ Subsemigroup.closure s := Subsemigroup.subset_closure hx

