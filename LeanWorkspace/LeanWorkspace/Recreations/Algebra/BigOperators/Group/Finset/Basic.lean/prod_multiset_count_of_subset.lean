import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_multiset_count_of_subset [DecidableEq M] (m : Multiset M) (s : Finset M)
    (hs : m.toFinset ⊆ s) : m.prod = ∏ i ∈ s, i ^ m.count i := by
  revert hs
  refine Quot.induction_on m fun l => ?_
  simp only [quot_mk_to_coe'', prod_coe, coe_count]
  apply Finset.prod_list_count_of_subset l s

