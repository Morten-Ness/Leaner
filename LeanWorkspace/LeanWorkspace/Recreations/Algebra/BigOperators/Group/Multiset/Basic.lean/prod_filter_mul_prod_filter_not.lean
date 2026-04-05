import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_filter_mul_prod_filter_not (p) [DecidablePred p] :
    (s.filter p).prod * (s.filter (fun a ↦ ¬ p a)).prod = s.prod := by
  rw [← Multiset.prod_add, filter_add_not]

