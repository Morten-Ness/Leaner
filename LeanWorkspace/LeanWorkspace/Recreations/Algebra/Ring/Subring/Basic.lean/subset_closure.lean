import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem subset_closure {s : Set R} : s ⊆ Subring.closure s := fun _ hx => Subring.mem_closure.2 fun _ hS => hS hx

