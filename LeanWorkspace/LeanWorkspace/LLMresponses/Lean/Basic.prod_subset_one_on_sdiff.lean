FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_subset_one_on_sdiff [DecidableEq ι] (h : s₁ ⊆ s₂) (hg : ∀ x ∈ s₂ \ s₁, g x = 1)
    (hfg : ∀ x ∈ s₁, f x = g x) : ∏ i ∈ s₁, f i = ∏ i ∈ s₂, g i := by
  rw [← Finset.prod_sdiff h]
  refine congrArg ((∏ i ∈ s₂ \ s₁, g i) * ·) ?_
  · exact Finset.prod_congr rfl (by intro x hx; exact hfg x (h hx))
  · rw [Finset.prod_eq_one]
    intro x hx
    exact hg x hx
