import Mathlib

variable {M A B : Type*}

variable [CommMonoid M] {x : M}

theorem mem_closure_finset {s : Finset M} :
    x ∈ closure s ↔ ∃ f : M → ℕ, f.support ⊆ s ∧ ∏ a ∈ s, a ^ f a = x where
  mp := by
    rw [Submonoid.mem_closure_iff_exists_finset_subset]
    rintro ⟨f, t, hts, hf, rfl⟩
    refine ⟨f, hf.trans hts, .symm <| Finset.prod_subset hts ?_⟩
    simp +contextual [Function.support_subset_iff'.1 hf]
  mpr := by rintro ⟨n, -, rfl⟩; exact Submonoid.prod_mem _ fun x hx ↦ pow_mem (subset_closure hx) _

