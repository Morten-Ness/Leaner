import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem list_prod_mem {l : List K} : (∀ x ∈ l, x ∈ s) → l.prod ∈ s := list_prod_mem

