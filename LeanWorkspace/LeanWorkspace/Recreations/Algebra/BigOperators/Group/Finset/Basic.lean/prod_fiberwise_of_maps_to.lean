import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}

variable [DecidableEq κ]

theorem prod_fiberwise_of_maps_to {g : ι → κ} (h : ∀ i ∈ s, g i ∈ t) (f : ι → M) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s, f i := by
  rw [← Finset.prod_disjiUnion, disjiUnion_filter_eq_of_maps_to h]
  #adaptation_note /-- 2025-09-12 (kmill) copied from private lemma pairwiseDisjoint_fibers -/
  intro x' hx y' hy hne
  simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

