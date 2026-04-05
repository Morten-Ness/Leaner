import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (s : Subring R)

theorem prod_mem {R : Type*} [CommRing R] (s : Subring R) {ι : Type*} {t : Finset ι}
    {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∏ i ∈ t, f i) ∈ s := prod_mem h

