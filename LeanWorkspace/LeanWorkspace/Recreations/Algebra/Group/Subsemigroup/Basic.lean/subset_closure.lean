import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem subset_closure : s ⊆ Subsemigroup.closure s := fun _ hx => Subsemigroup.mem_closure.2 fun _ hS => hS hx

