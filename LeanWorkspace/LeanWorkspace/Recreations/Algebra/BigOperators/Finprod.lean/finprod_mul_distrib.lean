import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mul_distrib (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    ∏ᶠ i, f i * g i = (∏ᶠ i, f i) * ∏ᶠ i, g i := by
  classical
    rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf Finset.subset_union_left,
      finprod_eq_prod_of_mulSupport_toFinset_subset g hg Finset.subset_union_right, ←
      Finset.prod_mul_distrib]
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    simp only [Finset.coe_union, Finite.coe_toFinset, mulSupport_subset_iff,
      mem_union, mem_mulSupport]
    intro x
    contrapose!
    rintro ⟨hf, hg⟩
    simp [hf, hg]

