import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_filter (p : ι → Prop) [DecidablePred p] (f : ι → M) :
    ∏ a ∈ s with p a, f a = ∏ a ∈ s, if p a then f a else 1 := calc
    ∏ a ∈ s with p a, f a = ∏ a ∈ s with p a, if p a then f a else 1 :=
      Finset.prod_congr rfl fun a h => by rw [if_pos]; simpa using (mem_filter.1 h).2
    _ = ∏ a ∈ s, if p a then f a else 1 := by
      { refine Finset.prod_subset (filter_subset _ s) fun x hs h => ?_
        rw [mem_filter, not_and] at h
        exact if_neg (by simpa using h hs) }

