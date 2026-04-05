import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem subset_closure {s : Set R} : s ⊆ Subsemiring.closure s := fun _ hx => Subsemiring.mem_closure.2 fun _ hS => hS hx

