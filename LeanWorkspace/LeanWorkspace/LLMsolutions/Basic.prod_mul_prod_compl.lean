FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_mul_prod_compl [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    (∏ i ∈ s, f i) * ∏ i ∈ sᶜ, f i = ∏ i, f i := by
  classical
  have hdisj : Disjoint s sᶜ := by
    exact Finset.disjoint_right.2 (by
      intro x hx hx'
      exact hx' hx)
  rw [← Finset.prod_union hdisj]
  simp
