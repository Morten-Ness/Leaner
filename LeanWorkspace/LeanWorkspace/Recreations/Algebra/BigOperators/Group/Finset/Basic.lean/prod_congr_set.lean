import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_congr_set [Fintype ι] (s : Set ι) [DecidablePred (· ∈ s)] (f : ι → M) (g : s → M)
    (w : ∀ x (hx : x ∈ s), f x = g ⟨x, hx⟩) (w' : ∀ x ∉ s, f x = 1) : ∏ i, f i = ∏ i, g i := by
  rw [← Finset.prod_subset s.toFinset.subset_univ (by simpa), Finset.prod_subtype (p := (· ∈ s)) _ (by simp)]
  congr! with ⟨x, h⟩
  exact w x h

