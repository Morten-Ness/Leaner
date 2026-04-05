import Mathlib

variable {ι α β M N G k R : Type*}

theorem prod_min_le [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M] {f g : ι → M} {s : Finset ι} :
    s.prod (fun i ↦ min (f i) (g i)) ≤ min (s.prod f) (s.prod g) := Multiset.prod_min_le

