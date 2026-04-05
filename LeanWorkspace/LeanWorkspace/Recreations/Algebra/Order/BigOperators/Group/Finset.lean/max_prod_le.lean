import Mathlib

variable {ι α β M N G k R : Type*}

theorem max_prod_le [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M] {f g : ι → M} {s : Finset ι} :
    max (s.prod f) (s.prod g) ≤ s.prod (fun i ↦ max (f i) (g i)) := Multiset.max_prod_le

