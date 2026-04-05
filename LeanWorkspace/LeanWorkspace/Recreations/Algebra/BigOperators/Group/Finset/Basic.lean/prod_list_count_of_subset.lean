import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_list_count_of_subset [DecidableEq M] (m : List M) (s : Finset M)
    (hs : m.toFinset ⊆ s) : m.prod = ∏ i ∈ s, i ^ m.count i := by
  rw [Finset.prod_list_count]
  refine Finset.prod_subset hs fun x _ hx => ?_
  rw [mem_toFinset] at hx
  rw [count_eq_zero_of_not_mem hx, pow_zero]

