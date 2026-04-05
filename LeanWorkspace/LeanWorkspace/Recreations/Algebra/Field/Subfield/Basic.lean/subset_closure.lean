import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem subset_closure {s : Set K} : s ⊆ Subfield.closure s := fun _ hx => Subfield.mem_closure.2 fun _ hS => hS hx

