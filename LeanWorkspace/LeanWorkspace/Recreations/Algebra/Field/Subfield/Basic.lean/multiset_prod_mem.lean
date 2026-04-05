import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Set K}

variable {K : Type u} [Field K] (s : Subfield K)

theorem multiset_prod_mem (m : Multiset K) : (∀ a ∈ m, a ∈ s) → m.prod ∈ s := multiset_prod_mem m

