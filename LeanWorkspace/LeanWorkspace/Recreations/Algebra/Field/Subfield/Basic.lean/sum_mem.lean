import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem sum_mem {ι : Type*} {t : Finset ι} {f : ι → K} (h : ∀ c ∈ t, f c ∈ s) :
    (∑ i ∈ t, f i) ∈ s := sum_mem h

