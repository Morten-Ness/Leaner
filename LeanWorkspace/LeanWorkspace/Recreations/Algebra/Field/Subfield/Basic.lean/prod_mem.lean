import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Set K}

variable {K : Type u} [Field K] (s : Subfield K)

theorem prod_mem {ι : Type*} {t : Finset ι} {f : ι → K} (h : ∀ c ∈ t, f c ∈ s) :
    (∏ i ∈ t, f i) ∈ s := prod_mem h

