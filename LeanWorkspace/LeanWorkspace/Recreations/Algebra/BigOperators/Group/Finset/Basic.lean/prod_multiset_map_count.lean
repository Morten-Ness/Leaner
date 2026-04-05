import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_multiset_map_count [DecidableEq ι] (s : Multiset ι) {M : Type*} [CommMonoid M]
    (f : ι → M) : (s.map f).prod = ∏ m ∈ s.toFinset, f m ^ s.count m := by
  refine Quot.induction_on s fun l => ?_
  simp [Finset.prod_list_map_count l f]

