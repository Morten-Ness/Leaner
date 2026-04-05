import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (s : Subring R)

theorem sum_mem {R : Type*} [Ring R] (s : Subring R) {ι : Type*} {t : Finset ι}
    {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∑ i ∈ t, f i) ∈ s := sum_mem h

