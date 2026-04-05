import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (s : Subring R)

theorem list_prod_mem {R} [Ring R] (s : Subring R) {l : List R} :
    (∀ x ∈ l, x ∈ s) → l.prod ∈ s := list_prod_mem

