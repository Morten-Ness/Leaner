FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_congr_set [Fintype ι] (s : Set ι) [DecidablePred (· ∈ s)] (f : ι → M) (g : s → M)
    (w : ∀ x (hx : x ∈ s), f x = g ⟨x, hx⟩) (w' : ∀ x ∉ s, f x = 1) : ∏ i, f i = ∏ i, g i := by
  classical
  let t : Finset ι := Finset.univ.filter (fun x => x ∈ s)
  have ht : ∀ x, x ∈ t ↔ x ∈ s := by
    intro x
    simp [t]
  calc
    (∏ i, f i) = ∏ i in t, f i := by
      rw [Finset.prod_filter]
      refine Finset.prod_congr rfl ?_
      intro x hx
      by_cases hs : x ∈ s
      · simp [hs]
      · simp [hs, w' x hs]
    _ = ∏ i in t, g ⟨i, (ht i).mp ‹i ∈ t›⟩ := by
      refine Finset.prod_congr rfl ?_
      intro x hx
      exact w x ((ht x).mp hx)
    _ = ∏ i : s, g i := by
      rw [← Finset.prod_attach]
      refine Finset.prod_congr rfl ?_
      intro x hx
      simp [t] at hx
      rfl
