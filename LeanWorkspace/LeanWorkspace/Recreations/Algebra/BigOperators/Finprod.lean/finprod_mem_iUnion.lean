import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_iUnion [Finite ι] {t : ι → Set α} (h : Pairwise (Disjoint on t))
    (ht : ∀ i, (t i).Finite) : ∏ᶠ a ∈ ⋃ i : ι, t i, f a = ∏ᶠ i, ∏ᶠ a ∈ t i, f a := by
  cases nonempty_fintype ι
  lift t to ι → Finset α using ht
  classical
    rw [← biUnion_univ, ← Finset.coe_univ, ← Finset.coe_biUnion, finprod_mem_coe_finset,
      Finset.prod_biUnion]
    · simp only [finprod_mem_coe_finset, finprod_eq_prod_of_fintype]
    · exact fun x _ y _ hxy => Finset.disjoint_coe.1 (h hxy)

