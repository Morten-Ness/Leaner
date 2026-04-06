FAIL
import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommRing R]

theorem prod_sub_ordered [LinearOrder ι] (s : Finset ι) (f g : ι → R) :
    ∏ i ∈ s, (f i - g i) =
      (∏ i ∈ s, f i) -
        ∑ i ∈ s, g i * (∏ j ∈ s with j < i, (f j - g j)) * ∏ j ∈ s with i < j, f j := by
  classical
  rw [Finset.prod_biUnion]
  · rw [sub_eq_add_neg, Finset.sum_neg_distrib]
    nth_rewrite 2 [← Finset.sum_singleton (a := ∏ i ∈ s, f i)]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_single ?_ ?_
    · intro t ht
      by_cases hs' : t = s
      · subst hs'
        simp
      · simp [hs', sub_eq_add_neg]
    · simp
  · intro a ha b hb hab
    simp [hab]
  · intro a ha
    simp
  · intro a ha
    exact {a}
  · ext t
    simp only [Finset.mem_bind, Finset.mem_singleton, exists_eq_right]
    constructor
    · intro ht
      simpa using ht
    · intro ht
      simp [ht]
