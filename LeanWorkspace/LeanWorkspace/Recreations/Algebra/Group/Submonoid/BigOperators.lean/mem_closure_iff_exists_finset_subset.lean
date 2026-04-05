import Mathlib

variable {M A B : Type*}

variable [CommMonoid M] {x : M}

theorem mem_closure_iff_exists_finset_subset {s : Set M} :
    x ∈ closure s ↔
      ∃ (f : M → ℕ) (t : Finset M), ↑t ⊆ s ∧ f.support ⊆ t ∧ ∏ a ∈ t, a ^ f a = x where
  mp hx := by
    classical
    induction hx using closure_induction with
    | one => exact ⟨0, ∅, by simp⟩
    | mem x hx =>
      simp only at hx
      exact ⟨Pi.single x 1, {x}, by simp [hx, Pi.single_apply]⟩
    | mul x y _ _ hx hy =>
    obtain ⟨f, t, hts, hf, rfl⟩ := hx
    obtain ⟨g, u, hus, hg, rfl⟩ := hy
    refine ⟨f + g, t ∪ u, mod_cast Set.union_subset hts hus,
      (Function.support_add _ _).trans <| mod_cast Set.union_subset_union hf hg, ?_⟩
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1 <;> symm
    · refine Finset.prod_subset Finset.subset_union_left ?_
      simp +contextual [Function.support_subset_iff'.1 hf]
    · refine Finset.prod_subset Finset.subset_union_right ?_
      simp +contextual [Function.support_subset_iff'.1 hg]
  mpr := by
    rintro ⟨n, t, hts, -, rfl⟩; exact Submonoid.prod_mem _ fun x hx ↦ pow_mem (subset_closure <| hts hx) _

