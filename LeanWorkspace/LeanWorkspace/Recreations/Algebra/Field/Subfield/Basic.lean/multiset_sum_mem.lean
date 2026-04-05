import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem multiset_sum_mem (m : Multiset K) : (∀ a ∈ m, a ∈ s) → m.sum ∈ s := multiset_sum_mem m

